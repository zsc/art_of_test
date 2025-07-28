# 第19章：并发测试

并发程序的正确性是软件工程中最具挑战性的问题之一。竞态条件、死锁、活锁等并发缺陷难以重现和调试。本章将系统介绍并发测试的理论基础、实用技术和工具支持。

## 19.1 并发缺陷的本质

并发编程引入了时间维度的不确定性，使得程序行为变得难以预测。理解并发缺陷的本质是设计有效测试策略的基础。并发缺陷不仅难以发现，更难以重现和调试，这使得系统化的测试方法变得尤为重要。

### 19.1.1 并发缺陷分类

并发缺陷可以从多个维度进行分类，每种类型都有其特定的表现形式和检测方法。

1. **竞态条件（Race Condition）**
   
   竞态条件是最常见的并发缺陷，发生在程序的正确性依赖于多个线程执行的相对时序时。主要包括：
   
   - **数据竞争（Data Race）**：多个线程同时访问共享数据，且至少有一个是写操作，没有适当的同步机制保护。数据竞争可能导致内存损坏、计算错误或程序崩溃。
   
   - **顺序违反（Order Violation）**：程序假设某些操作会按特定顺序执行，但并发执行破坏了这种假设。例如，一个线程假设另一个线程已经完成初始化，但实际上初始化可能尚未完成。
   
   - **原子性违反（Atomicity Violation）**：一组操作在逻辑上应该原子执行（要么全部完成，要么全部不执行），但在并发环境下被其他线程的操作打断。典型例子是check-then-act模式，如先检查条件再执行操作。

2. **死锁（Deadlock）**
   
   死锁发生在一组线程相互等待对方持有的资源，导致所有线程都无法继续执行。死锁的四个必要条件（Coffman条件）：
   
   - **互斥访问（Mutual Exclusion）**：资源不能被多个线程同时使用
   - **持有并等待（Hold and Wait）**：线程持有至少一个资源，同时等待获取其他资源
   - **不可剥夺（No Preemption）**：资源只能由持有者主动释放，不能被强制剥夺
   - **循环等待（Circular Wait）**：存在一个线程的循环链，每个线程都在等待下一个线程持有的资源
   
   理解这些条件对于设计死锁预防和检测策略至关重要。

3. **活锁（Livelock）**
   
   活锁是一种特殊的并发问题，线程并未被阻塞，但由于不断地响应其他线程的动作而无法取得进展。常见场景包括：
   
   - **过度礼让**：两个线程都试图避让对方，结果都无法前进，类似两个人在走廊相遇时不断左右避让
   - **重试风暴**：大量线程同时重试失败的操作，导致系统过载，所有重试都继续失败
   - **优先级反转处理不当**：高优先级线程不断让步给低优先级线程

4. **饥饿（Starvation）**
   
   饥饿发生在某些线程长期无法获得所需资源或执行机会。可能的原因包括：
   
   - **不公平的调度策略**：某些线程总是被优先考虑，其他线程很少获得执行机会
   - **资源分配不均**：某些线程总是能获得资源，而其他线程始终等待
   - **优先级设置不当**：低优先级线程在高负载情况下永远得不到执行
   
   饥饿虽然不会导致系统完全停止，但会严重影响系统的响应性和公平性。

### 19.1.2 并发测试的挑战

并发测试面临着独特的挑战，这些挑战源于并发执行的本质特性。理解这些挑战有助于选择合适的测试策略和工具。

**1. 非确定性（Non-determinism）**

并发程序的最大特点是执行的非确定性。相同的输入在不同运行中可能产生不同的结果，这是由于：
- 线程调度的不可预测性：操作系统调度器的决策受多种因素影响
- 硬件层面的不确定性：缓存命中率、内存访问延迟等
- 外部事件的影响：中断、I/O操作完成时间等

这种非确定性使得传统的"运行一次通过即可"的测试方法失效。

**2. 调度敏感性（Schedule Sensitivity）**

许多并发缺陷只在特定的线程交错执行顺序下才会显现。考虑两个线程各执行n条指令，可能的交错方式数量是C(2n,n)，随着n增长呈指数级增长。在实际测试中，我们只能覆盖极小一部分可能的调度。

**3. 海森堡效应（Heisenberg Effect）**

这个术语借用自量子物理，描述了观测行为本身改变被观测系统的现象。在并发测试中表现为：
- 添加日志语句可能改变线程时序，使原本存在的bug消失
- 调试器的介入改变程序执行特性
- 性能监控工具影响线程调度

这使得调试并发程序变得极其困难。

**4. 状态空间爆炸（State Space Explosion）**

并发系统的状态空间随着线程数量和同步点数量呈指数增长。完全探索所有可能状态在实践中是不可行的，必须采用智能的剪枝和采样策略。

**5. 硬件和平台依赖性**

并发行为强烈依赖于底层硬件和平台：
- CPU核心数影响实际的并行度
- 内存模型（如x86的TSO vs ARM的弱内存模型）影响指令重排
- 缓存架构影响false sharing等性能问题
- 不同操作系统的调度策略差异

**6. 时间相关性（Timing Dependencies）**

某些并发缺陷只在特定的时间窗口内出现：
- 竞态条件可能需要精确的时间对齐
- 性能相关的并发问题（如惊群效应）只在高负载下出现
- 某些缺陷需要特定的执行速度比例

```python
class ConcurrencyTestingChallenges:
    def why_concurrent_bugs_are_hard(self):
        """总结并发缺陷难以测试的原因"""
        return {
            "非确定性": "相同输入可能产生不同结果，难以重现问题",
            "调度敏感": "错误依赖特定的线程调度序列",
            "海森堡效应": "观测和调试行为改变程序执行特性",
            "状态空间爆炸": "可能的交错执行数量随线程数指数增长",
            "硬件依赖": "不同硬件架构和配置表现不同",
            "时间窗口": "某些缺陷只在极短的时间窗口内可观察",
            "复合效应": "多个并发缺陷相互作用，增加复杂性"
        }
    
    def quantify_interleaving_space(self, num_threads, instructions_per_thread):
        """量化可能的交错执行空间大小"""
        # 对于n个线程，每个执行m条指令
        # 可能的交错数量是多项式系数
        from math import factorial
        
        total_instructions = num_threads * instructions_per_thread
        
        # 计算多项式系数：(n*m)! / (m!)^n
        numerator = factorial(total_instructions)
        denominator = factorial(instructions_per_thread) ** num_threads
        
        return numerator // denominator
    
    def demonstrate_nondeterminism(self):
        """演示并发的非确定性"""
        # 一个简单但具有教育意义的例子
        # 展示了即使是最简单的并发程序也可能出现意外行为
        
        # 示例：两个线程递增共享计数器
        # 每个线程执行：读取 -> 计算 -> 写入
        # 可能的交错：
        # 1. T1读(0) -> T1算(1) -> T1写(1) -> T2读(1) -> T2算(2) -> T2写(2) ✓
        # 2. T1读(0) -> T2读(0) -> T1算(1) -> T2算(1) -> T1写(1) -> T2写(1) ✗
        # 3. T1读(0) -> T2读(0) -> T2算(1) -> T1算(1) -> T2写(1) -> T1写(1) ✗
        # ... 还有更多可能
        
        # 这个简单例子展示了：
        # - 6个操作有20种可能的交错方式
        # - 其中只有部分能产生正确结果
        # - 实际运行时哪种交错发生是不确定的
        pass
```

### 19.1.3 happens-before关系

happens-before关系是理解和分析并发程序行为的核心概念。它定义了操作之间的偏序关系，帮助我们推理哪些执行顺序是合法的，哪些可能导致数据竞争。

**happens-before的定义**

如果操作A happens-before操作B（记作A → B），意味着：
- A的效果对B可见
- A在逻辑时间上先于B发生
- 不存在数据竞争的情况下，B能观察到A的结果

重要的是，happens-before是偏序关系，不是全序。两个操作可能没有happens-before关系，这时它们被认为是并发的。

**基本的happens-before规则**

1. **程序顺序规则（Program Order Rule）**
   - 在同一个线程内，按照程序代码顺序，前面的操作happens-before后面的操作
   - 这保证了单线程程序的语义

2. **监视器锁规则（Monitor Lock Rule）**
   - 对一个锁的unlock操作happens-before后续对同一个锁的lock操作
   - 这确保了临界区的互斥访问和可见性

3. **volatile变量规则**
   - 对volatile变量的写操作happens-before后续对同一变量的读操作
   - volatile提供了轻量级的同步机制

4. **线程启动规则（Thread Start Rule）**
   - Thread.start()的调用happens-before被启动线程中的任何操作
   - 确保线程启动前的初始化对新线程可见

5. **线程终止规则（Thread Termination Rule）**
   - 线程中的任何操作happens-before其他线程从Thread.join()成功返回
   - 保证线程结束后其结果对其他线程可见

6. **中断规则（Interruption Rule）**
   - 对线程interrupt()的调用happens-before被中断线程检测到中断事件

7. **传递性规则（Transitivity）**
   - 如果A happens-before B，且B happens-before C，则A happens-before C
   - 这允许我们链接多个happens-before关系进行推理

```python
class HappensBeforeRelation:
    def basic_rules(self):
        """happens-before的基本规则及其含义"""
        return {
            "程序顺序规则": {
                "描述": "同一线程内的操作按程序顺序排序",
                "示例": "int a = 1; int b = 2; // a的赋值 happens-before b的赋值",
                "作用": "保证单线程语义"
            },
            "监视器锁规则": {
                "描述": "unlock操作 happens-before 后续的lock操作",
                "示例": "线程1 unlock(m) happens-before 线程2 lock(m)",
                "作用": "确保临界区的可见性"
            },
            "volatile规则": {
                "描述": "volatile写 happens-before volatile读",
                "示例": "volatile_write(v, 1) happens-before volatile_read(v)",
                "作用": "轻量级同步"
            },
            "线程启动规则": {
                "描述": "start() happens-before 线程内的任何操作",
                "示例": "parent.start(child) happens-before child.run()",
                "作用": "初始化可见性"
            },
            "线程终止规则": {
                "描述": "线程内操作 happens-before join()返回",
                "示例": "child.operation() happens-before parent.join(child)",
                "作用": "结果可见性"
            }
        }
    
    def construct_happens_before_graph(self, execution_trace):
        """从执行轨迹构建happens-before图"""
        # happens-before图是一个有向无环图(DAG)
        # 节点是内存操作，边表示happens-before关系
        
        graph = {}  # operation -> set of operations it happens-before
        
        # 1. 添加程序顺序边
        for thread_ops in execution_trace.get_thread_operations():
            for i in range(len(thread_ops) - 1):
                self.add_edge(graph, thread_ops[i], thread_ops[i+1])
        
        # 2. 添加同步边
        for sync_pair in execution_trace.get_synchronization_pairs():
            self.add_edge(graph, sync_pair.release, sync_pair.acquire)
        
        # 3. 计算传递闭包
        self.transitive_closure(graph)
        
        return graph
    
    def detect_concurrent_operations(self, hb_graph, op1, op2):
        """检测两个操作是否并发（没有happens-before关系）"""
        # 如果 op1 → op2 或 op2 → op1，则它们有序
        # 否则它们是并发的
        
        if op2 in hb_graph.get(op1, set()):
            return False  # op1 happens-before op2
        
        if op1 in hb_graph.get(op2, set()):
            return False  # op2 happens-before op1
        
        return True  # 并发操作
    
    def identify_race_conditions(self, hb_graph, memory_accesses):
        """使用happens-before关系识别潜在的数据竞争"""
        races = []
        
        # 对每对访问同一内存位置的操作
        for loc in memory_accesses:
            ops = memory_accesses[loc]
            for i, op1 in enumerate(ops):
                for op2 in ops[i+1:]:
                    # 至少一个是写操作
                    if op1.is_write or op2.is_write:
                        # 检查是否并发
                        if self.detect_concurrent_operations(hb_graph, op1, op2):
                            races.append((op1, op2, loc))
        
        return races
```

### 练习 19.1

<details>
<summary>点击查看练习</summary>

**问题1**：分析以下银行账户类的潜在并发问题，并提出修复方案。

```java
class BankAccount {
    private int balance;
    
    public void deposit(int amount) {
        balance = balance + amount;
    }
    
    public void withdraw(int amount) {
        if (balance >= amount) {
            balance = balance - amount;
        }
    }
    
    public void transfer(BankAccount to, int amount) {
        this.withdraw(amount);
        to.deposit(amount);
    }
}
```

**问题2**：画出两个线程同时调用deposit(100)时可能的执行交错，并说明哪些交错会导致错误结果。

**问题3**：如果我们简单地在每个方法上加synchronized，transfer方法还会有什么问题？

**参考答案**：

1. **识别的并发问题**：

   a) **数据竞争（Data Race）**
   - `balance = balance + amount`不是原子操作，实际包含三步：读取balance、计算新值、写回balance
   - 多个线程同时执行时，可能读到相同的旧值，导致更新丢失
   
   b) **原子性违反（Atomicity Violation）**
   - transfer方法逻辑上应该是原子操作（要么全部成功，要么全部失败）
   - 当前实现中，withdraw成功后如果线程被中断，deposit可能不执行
   - 更糟的是，如果withdraw检查通过但执行前其他线程修改了余额，可能导致透支
   
   c) **检查-然后-执行（Check-Then-Act）竞态**
   - withdraw方法中，检查余额和实际扣款之间存在时间窗口
   - 其他线程可能在这个窗口内修改余额，导致透支
   
   d) **潜在死锁（Potential Deadlock）**
   - 如果两个线程同时执行相反方向的转账（A→B和B→A）
   - 使用简单的同步可能导致循环等待

2. **deposit(100)的执行交错分析**：

   假设初始balance = 1000，两个线程T1和T2同时调用deposit(100)：
   
   正确的交错（结果=1200）：
   ```
   T1: read balance (1000)
   T1: compute 1000+100
   T1: write balance (1100)
   T2: read balance (1100)
   T2: compute 1100+100
   T2: write balance (1200) ✓
   ```
   
   错误的交错（结果=1100，丢失更新）：
   ```
   T1: read balance (1000)
   T2: read balance (1000)  // 也读到1000
   T1: compute 1000+100
   T2: compute 1000+100     // 都计算出1100
   T1: write balance (1100)
   T2: write balance (1100) ✗ // T1的更新丢失
   ```

3. **简单synchronized的问题**：

   ```java
   public synchronized void transfer(BankAccount to, int amount) {
       this.withdraw(amount);  // 释放this的锁
       to.deposit(amount);     // 尝试获取to的锁
   }
   ```
   
   问题：
   - synchronized是可重入的，但只对同一个对象
   - withdraw调用会成功（同一对象），但deposit需要获取另一个账户的锁
   - 如果A.transfer(B, 100)和B.transfer(A, 200)同时执行，可能死锁

**完整的修复方案**：

```java
class BankAccount {
    private int balance;
    private final long id;  // 用于锁顺序
    
    public synchronized void deposit(int amount) {
        balance = balance + amount;
    }
    
    public synchronized void withdraw(int amount) throws InsufficientFundsException {
        if (balance < amount) {
            throw new InsufficientFundsException();
        }
        balance = balance - amount;
    }
    
    public void transfer(BankAccount to, int amount) throws InsufficientFundsException {
        // 按ID顺序获取锁，避免死锁
        BankAccount first = this.id < to.id ? this : to;
        BankAccount second = this.id < to.id ? to : this;
        
        synchronized(first) {
            synchronized(second) {
                this.withdraw(amount);
                to.deposit(amount);
            }
        }
    }
}
```

**进一步思考**：
- 这个解决方案假设了账户ID的唯一性和不变性
- 在高并发场景下，全局锁顺序可能成为瓶颈
- 考虑使用更细粒度的锁或无锁算法进行优化

</details>

## 19.2 系统化的并发测试方法

有效的并发测试需要系统化的方法论。本节介绍几种经过实践验证的并发测试技术，每种都有其适用场景和优缺点。

### 19.2.1 压力测试

压力测试是最直观的并发测试方法，通过创造高并发、高负载的环境来增加暴露并发缺陷的概率。虽然不能保证发现所有问题，但实践证明这是发现常见并发缺陷的有效方法。

**压力测试的核心策略**

1. **超额订阅（Over-subscription）**
   - 创建远超CPU核心数的线程，强制频繁的上下文切换
   - 增加线程交错的多样性

2. **同步启动（Synchronized Start）**
   - 使用屏障或闭锁让所有线程同时开始执行
   - 最大化竞争窗口

3. **负载变化（Load Variation）**
   - 改变工作负载大小，测试不同压力下的行为
   - 某些缺陷只在特定负载水平下出现

4. **资源竞争（Resource Contention）**
   - 故意创造资源瓶颈，如减少连接池大小
   - 暴露资源管理相关的并发问题

```python
class StressTesting:
    def design_stress_test(self, target_function, shared_resource):
        """设计综合性压力测试框架"""
        
        class StressTestConfig:
            def __init__(self):
                self.thread_counts = [1, 2, 4, 8, 16, 32, 64, 128]  # 递增的线程数
                self.iterations = 10000
                self.warmup_iterations = 100
                self.barrier_sync = True  # 是否同步启动
                self.inject_delays = True  # 是否注入随机延迟
                self.monitor_performance = True
        
        def stress_test_framework(config):
            results = {
                'errors': [],
                'performance': {},
                'invariant_violations': []
            }
            
            for num_threads in config.thread_counts:
                print(f"Testing with {num_threads} threads...")
                
                # 1. 预热阶段 - JIT编译优化，缓存预热
                if config.warmup_iterations > 0:
                    self._warmup(target_function, shared_resource, 
                                config.warmup_iterations)
                
                # 2. 压力测试主循环
                start_time = time.time()
                errors_at_level = 0
                
                for iteration in range(config.iterations):
                    # 重置共享资源到已知状态
                    shared_resource.reset()
                    
                    # 创建线程
                    threads = []
                    if config.barrier_sync:
                        barrier = threading.Barrier(num_threads)
                    
                    for i in range(num_threads):
                        t = Thread(
                            target=self._worker,
                            args=(target_function, shared_resource, 
                                  barrier if config.barrier_sync else None,
                                  config.inject_delays)
                        )
                        threads.append(t)
                    
                    # 启动所有线程
                    for t in threads:
                        t.start()
                    
                    # 等待完成
                    for t in threads:
                        t.join()
                    
                    # 3. 验证不变量
                    violations = self._check_invariants(shared_resource)
                    if violations:
                        results['invariant_violations'].extend(violations)
                        errors_at_level += 1
                
                # 记录性能数据
                elapsed = time.time() - start_time
                results['performance'][num_threads] = {
                    'total_time': elapsed,
                    'ops_per_second': (config.iterations * num_threads) / elapsed,
                    'error_rate': errors_at_level / config.iterations
                }
            
            return results
    
    def _worker(self, target_function, shared_resource, barrier, inject_delays):
        """工作线程的执行逻辑"""
        if barrier:
            barrier.wait()  # 同步启动
        
        try:
            if inject_delays and random.random() < 0.1:
                # 10%概率注入0-10ms的随机延迟
                time.sleep(random.uniform(0, 0.01))
            
            target_function(shared_resource)
            
        except Exception as e:
            # 记录但不抛出异常，继续测试
            self._log_error(e)
    
    def _check_invariants(self, shared_resource):
        """检查共享资源的不变量"""
        violations = []
        
        # 示例不变量检查
        if hasattr(shared_resource, 'check_consistency'):
            if not shared_resource.check_consistency():
                violations.append({
                    'type': 'consistency',
                    'details': shared_resource.get_state()
                })
        
        if hasattr(shared_resource, 'total_sum'):
            expected = shared_resource.get_expected_sum()
            actual = shared_resource.total_sum()
            if expected != actual:
                violations.append({
                    'type': 'sum_mismatch',
                    'expected': expected,
                    'actual': actual
                })
        
        return violations
    
    def adaptive_stress_test(self, target_function, shared_resource):
        """自适应压力测试：根据错误率动态调整参数"""
        
        config = {
            'threads': 4,
            'iterations': 100,
            'delay_probability': 0.0
        }
        
        while config['iterations'] < 10000:
            error_rate = self._run_test_round(target_function, shared_resource, config)
            
            if error_rate == 0:
                # 没有发现错误，增加压力
                config['threads'] *= 2
                config['delay_probability'] += 0.1
            elif error_rate > 0.5:
                # 错误率过高，稍微降低压力以获得更稳定的重现
                config['threads'] = max(1, config['threads'] // 2)
            
            # 如果发现错误，增加迭代次数以收集更多数据
            if error_rate > 0:
                config['iterations'] *= 2
            
            print(f"Adjusted config: {config}, error_rate: {error_rate}")
```

### 19.2.2 调度探索

压力测试依赖随机性，可能错过罕见但重要的执行序列。调度探索技术通过系统化地控制线程调度来提供更强的保证。这类技术的核心思想是将非确定性的调度转化为可控的、可重现的执行序列。

**调度探索的关键概念**

1. **调度决策点（Scheduling Decision Points）**
   - 程序中可能发生线程切换的位置
   - 包括同步操作、共享内存访问、系统调用等

2. **调度空间（Schedule Space）**
   - 所有可能的线程交错执行序列的集合
   - 大小随程序复杂度呈指数增长

3. **探索策略（Exploration Strategy）**
   - 如何选择要测试的调度序列
   - 平衡覆盖率和测试时间

```python
class ScheduleExploration:
    def systematic_exploration(self):
        """系统化探索可能的调度序列"""
        
        class ScheduleController:
            def __init__(self):
                self.decision_points = []  # 记录所有决策点
                self.current_schedule = []  # 当前执行的调度序列
                self.explored_schedules = set()  # 已探索的调度
                self.pending_schedules = []  # 待探索的调度
                self.execution_tree = {}  # 执行树结构
            
            def at_decision_point(self, active_threads, current_thread):
                """在调度决策点被调用"""
                
                # 记录决策点信息
                decision_point = {
                    'id': len(self.decision_points),
                    'active_threads': active_threads.copy(),
                    'current_thread': current_thread,
                    'location': self.get_program_location()
                }
                self.decision_points.append(decision_point)
                
                # 如果正在重放，按照预定调度执行
                if self.is_replaying():
                    return self.get_next_scheduled_thread()
                
                # 否则，选择下一个线程并记录
                next_thread = self.make_scheduling_decision(active_threads)
                self.current_schedule.append((decision_point['id'], next_thread))
                
                # 记录其他可能的选择供后续探索
                for thread in active_threads:
                    if thread != next_thread:
                        alternative = self.current_schedule[:-1] + [(decision_point['id'], thread)]
                        if tuple(alternative) not in self.explored_schedules:
                            self.pending_schedules.append(alternative)
                
                return next_thread
            
            def make_scheduling_decision(self, active_threads):
                """决定下一个要执行的线程"""
                # 策略1: 深度优先 - 总是选择ID最小的线程
                # return min(active_threads, key=lambda t: t.id)
                
                # 策略2: 随机选择增加多样性
                # return random.choice(active_threads)
                
                # 策略3: 优先级引导 - 基于历史信息
                return self.priority_guided_choice(active_threads)
            
            def explore_all_schedules(self):
                """系统化探索所有可能的调度"""
                
                # 初始执行
                self.run_program()
                self.explored_schedules.add(tuple(self.current_schedule))
                
                # 探索所有待定调度
                while self.pending_schedules:
                    next_schedule = self.pending_schedules.pop()
                    
                    # 检查是否值得探索（剪枝）
                    if self.should_explore(next_schedule):
                        self.replay_schedule(next_schedule)
                        self.explored_schedules.add(tuple(next_schedule))
                
                return len(self.explored_schedules)
    
    def partial_order_reduction(self):
        """偏序约简技术减少需要探索的调度数量"""
        
        class PORAnalyzer:
            def __init__(self):
                self.independence_cache = {}  # 缓存独立性分析结果
            
            def are_independent(self, op1, op2):
                """判断两个操作是否独立"""
                
                # 查缓存
                key = (op1, op2) if op1 < op2 else (op2, op1)
                if key in self.independence_cache:
                    return self.independence_cache[key]
                
                # 独立性条件：
                # 1. 不访问相同的共享变量
                # 2. 或都是读操作
                # 3. 不涉及相同的同步对象
                
                independent = True
                
                # 检查内存访问
                if op1.memory_access and op2.memory_access:
                    if op1.address == op2.address:
                        if op1.is_write or op2.is_write:
                            independent = False
                
                # 检查同步操作
                if op1.sync_object and op2.sync_object:
                    if op1.sync_object == op2.sync_object:
                        independent = False
                
                self.independence_cache[key] = independent
                return independent
            
            def compute_persistent_set(self, state, enabled_transitions):
                """计算持久集 - 只需要探索的转换子集"""
                
                # 如果只有一个可能的转换，返回它
                if len(enabled_transitions) == 1:
                    return enabled_transitions
                
                # 寻找与其他所有转换都独立的转换
                for t in enabled_transitions:
                    if all(self.are_independent(t, other) 
                          for other in enabled_transitions if other != t):
                        return [t]  # 只需要探索这一个
                
                # 否则需要探索所有转换
                return enabled_transitions
    
    def sleep_set_optimization(self):
        """睡眠集优化进一步减少冗余探索"""
        
        class SleepSetOptimizer:
            def __init__(self):
                self.sleep_sets = {}  # state -> set of sleeping transitions
            
            def update_sleep_set(self, current_state, executed_transition, next_state):
                """更新睡眠集"""
                
                # 从当前状态的睡眠集开始
                current_sleep = self.sleep_sets.get(current_state, set())
                next_sleep = set()
                
                # 保留与执行转换独立的睡眠转换
                for sleeping in current_sleep:
                    if self.are_independent(sleeping, executed_transition):
                        next_sleep.add(sleeping)
                
                # 添加被跳过的使能转换
                enabled = self.get_enabled_transitions(current_state)
                for t in enabled:
                    if t != executed_transition and t not in current_sleep:
                        # 如果这个转换与执行的转换独立，加入睡眠集
                        if self.are_independent(t, executed_transition):
                            next_sleep.add(t)
                
                self.sleep_sets[next_state] = next_sleep
```

### 19.2.3 延迟注入

延迟注入是一种轻量级但有效的并发测试技术。通过在程序的关键位置注入随机或有策略的延迟，可以改变线程的执行时序，增加暴露并发缺陷的概率。这种方法的优势在于实现简单，对原程序的侵入性小。

**延迟注入的原理**

并发缺陷往往需要特定的时序条件才能触发。在正常执行中，这些时序窗口可能非常短暂。延迟注入通过人为地延长或调整这些时间窗口，使得原本罕见的交错变得更容易发生。

**注入策略**

1. **位置选择**：在哪些地方注入延迟
2. **延迟大小**：注入多长时间的延迟
3. **触发条件**：什么情况下注入延迟
4. **自适应调整**：根据测试效果动态调整策略

```python
class DelayInjection:
    def __init__(self):
        self.injection_stats = {}  # 统计注入效果
        self.adaptive_delays = {}  # 自适应延迟参数
        
    def inject_delays(self, program):
        """智能延迟注入框架"""
        
        class DelayInjector:
            def __init__(self, strategy='adaptive'):
                self.strategy = strategy
                self.injection_points = {
                    'pre_lock': {'base_delay': 0.001, 'variance': 0.005},
                    'post_unlock': {'base_delay': 0.002, 'variance': 0.003},
                    'pre_read': {'base_delay': 0.0005, 'variance': 0.001},
                    'post_write': {'base_delay': 0.001, 'variance': 0.002},
                    'thread_yield': {'base_delay': 0.0, 'variance': 0.01}
                }
                self.injection_history = []
                
            def should_inject(self, point_type, context):
                """决定是否在此处注入延迟"""
                
                if self.strategy == 'always':
                    return True
                    
                elif self.strategy == 'random':
                    # 基于概率的注入
                    probabilities = {
                        'pre_lock': 0.3,      # 30%概率在锁前注入
                        'post_unlock': 0.2,   # 20%概率在解锁后注入
                        'pre_read': 0.1,      # 10%概率在读前注入
                        'post_write': 0.15,   # 15%概率在写后注入
                        'thread_yield': 0.05  # 5%概率主动让步
                    }
                    return random.random() < probabilities.get(point_type, 0.1)
                    
                elif self.strategy == 'adaptive':
                    # 基于历史效果自适应调整
                    return self.adaptive_decision(point_type, context)
                    
                elif self.strategy == 'pattern':
                    # 基于特定模式注入
                    return self.pattern_based_decision(point_type, context)
            
            def calculate_delay(self, point_type, context):
                """计算注入的延迟时长"""
                
                config = self.injection_points[point_type]
                base = config['base_delay']
                variance = config['variance']
                
                if self.strategy == 'adaptive':
                    # 根据竞争程度调整延迟
                    contention_level = self.estimate_contention(context)
                    base *= (1 + contention_level)
                
                # 添加随机性
                delay = base + random.uniform(-variance, variance)
                
                # 确保延迟为正
                return max(0, delay)
            
            def inject(self, point_type, context, operation):
                """执行延迟注入"""
                
                if self.should_inject(point_type, context):
                    delay = self.calculate_delay(point_type, context)
                    
                    # 记录注入信息
                    injection_info = {
                        'timestamp': time.time(),
                        'thread_id': threading.current_thread().ident,
                        'point_type': point_type,
                        'delay': delay,
                        'context': context
                    }
                    self.injection_history.append(injection_info)
                    
                    # 执行延迟
                    if delay > 0:
                        time.sleep(delay)
                    
                    # 可选：主动触发调度
                    if point_type == 'thread_yield':
                        thread_yield()  # 平台相关的线程让步
            
            def adaptive_decision(self, point_type, context):
                """自适应决策：根据历史效果调整注入策略"""
                
                # 分析最近的注入效果
                recent_injections = self.get_recent_injections(point_type)
                
                if not recent_injections:
                    return True  # 首次注入
                
                # 计算效果指标
                bug_discovery_rate = self.calculate_bug_discovery_rate(recent_injections)
                performance_impact = self.calculate_performance_impact(recent_injections)
                
                # 平衡bug发现率和性能影响
                if bug_discovery_rate > 0.1:  # 发现bug率高
                    return True
                elif performance_impact > 0.5:  # 性能影响过大
                    return False
                else:
                    # 逐渐增加注入概率
                    return random.random() < (0.1 + bug_discovery_rate * 0.5)
            
            def pattern_based_decision(self, point_type, context):
                """基于模式的注入：识别特定的代码模式"""
                
                patterns = {
                    'double_checked_locking': {
                        'locations': ['pre_lock', 'post_read'],
                        'condition': lambda ctx: ctx.get('is_dcl_pattern')
                    },
                    'producer_consumer': {
                        'locations': ['post_write', 'pre_read'],
                        'condition': lambda ctx: ctx.get('is_queue_operation')
                    },
                    'reader_writer': {
                        'locations': ['pre_lock', 'post_unlock'],
                        'condition': lambda ctx: ctx.get('is_rw_lock')
                    }
                }
                
                for pattern_name, pattern_config in patterns.items():
                    if point_type in pattern_config['locations']:
                        if pattern_config['condition'](context):
                            return True
                
                return False
        
        # 创建注入器并应用到程序
        injector = DelayInjector()
        
        # 包装同步原语
        def wrap_lock_acquire(original_acquire):
            def wrapped(*args, **kwargs):
                injector.inject('pre_lock', {'lock': args[0]}, None)
                result = original_acquire(*args, **kwargs)
                return result
            return wrapped
        
        def wrap_lock_release(original_release):
            def wrapped(*args, **kwargs):
                result = original_release(*args, **kwargs)
                injector.inject('post_unlock', {'lock': args[0]}, None)
                return result
            return wrapped
        
        # 返回注入器供程序使用
        return injector
    
    def targeted_delay_injection(self):
        """针对性延迟注入：专门针对已知的并发模式"""
        
        class TargetedInjector:
            def __init__(self):
                self.target_patterns = [
                    'race_on_check',      # 检查时的竞态
                    'lost_notify',        # 丢失的通知
                    'aba_problem',        # ABA问题
                    'priority_inversion'  # 优先级反转
                ]
            
            def inject_for_race_on_check(self, check_operation, action_operation):
                """在check和action之间注入延迟"""
                
                def wrapped_check(*args, **kwargs):
                    result = check_operation(*args, **kwargs)
                    # 在检查后注入延迟，增加其他线程介入的机会
                    time.sleep(random.uniform(0.01, 0.05))
                    return result
                
                return wrapped_check
            
            def inject_for_lost_notify(self, wait_operation, notify_operation):
                """测试丢失通知的情况"""
                
                def wrapped_wait(*args, **kwargs):
                    # 在等待前注入延迟，可能错过通知
                    if random.random() < 0.3:
                        time.sleep(0.02)
                    return wait_operation(*args, **kwargs)
                
                return wrapped_wait
```

### 练习 19.2

<details>
<summary>点击查看练习</summary>

**问题1**：设计一个测试框架来系统化地检测ABA问题。ABA问题是指一个值从A变为B，然后又变回A，使得基于值比较的并发算法错误地认为值没有改变。

**问题2**：实现一个调度探索器，能够找出导致特定不变量违反的最短执行序列。

**问题3**：设计一个延迟注入策略，专门用于暴露生产者-消费者模式中的并发缺陷。

**参考答案**：

**答案1：ABA问题检测框架**

```python
class ABADetector:
    """全面的ABA问题检测框架"""
    
    def __init__(self):
        self.value_history = {}  # address -> [(value, thread, timestamp, version)]
        self.access_log = []      # 所有内存访问的日志
        self.aba_patterns = []    # 检测到的ABA模式
        self.version_counters = {}  # 为每个地址维护版本号
        
    def monitor_memory_access(self, address, value, access_type, thread_id=None):
        """监控所有内存访问"""
        
        if thread_id is None:
            thread_id = threading.current_thread().ident
            
        timestamp = time.time()
        
        # 记录访问
        access_info = {
            'address': address,
            'value': value,
            'type': access_type,  # 'read', 'write', 'cas'
            'thread': thread_id,
            'timestamp': timestamp
        }
        self.access_log.append(access_info)
        
        # 更新值历史
        if address not in self.value_history:
            self.value_history[address] = []
            self.version_counters[address] = 0
        
        if access_type in ['write', 'cas']:
            # 递增版本号
            self.version_counters[address] += 1
            
            self.value_history[address].append({
                'value': value,
                'thread': thread_id,
                'timestamp': timestamp,
                'version': self.version_counters[address]
            })
            
            # 检测ABA模式
            self._detect_aba_pattern(address)
    
    def _detect_aba_pattern(self, address):
        """检测给定地址的ABA模式"""
        
        history = self.value_history[address]
        
        if len(history) < 3:
            return
        
        # 检查最近的值变化
        for i in range(len(history) - 2):
            for j in range(i + 2, len(history)):
                if history[i]['value'] == history[j]['value']:
                    # 找到A...A模式，检查中间是否有不同值
                    intermediate_values = [h['value'] for h in history[i+1:j]]
                    if intermediate_values and any(v != history[i]['value'] for v in intermediate_values):
                        # 发现ABA模式
                        aba_info = {
                            'address': address,
                            'pattern': history[i:j+1],
                            'start_version': history[i]['version'],
                            'end_version': history[j]['version'],
                            'duration': history[j]['timestamp'] - history[i]['timestamp'],
                            'threads_involved': list(set(h['thread'] for h in history[i:j+1]))
                        }
                        self.aba_patterns.append(aba_info)
                        
                        # 分析潜在影响
                        self._analyze_aba_impact(aba_info)
    
    def _analyze_aba_impact(self, aba_info):
        """分析ABA问题的潜在影响"""
        
        # 查找在ABA期间的CAS操作
        start_time = aba_info['pattern'][0]['timestamp']
        end_time = aba_info['pattern'][-1]['timestamp']
        address = aba_info['address']
        
        affected_cas = []
        for access in self.access_log:
            if (access['type'] == 'cas' and 
                access['address'] == address and
                start_time <= access['timestamp'] <= end_time):
                affected_cas.append(access)
        
        if affected_cas:
            print(f"WARNING: {len(affected_cas)} CAS operations potentially affected by ABA")
            
    def create_aba_test_scenario(self):
        """创建各种ABA测试场景"""
        
        scenarios = []
        
        # 场景1：简单的ABA
        def simple_aba():
            shared_value = {'data': 'A', 'count': 0}
            
            def reader_thread():
                # 读取初始值
                initial = shared_value['data']
                self.monitor_memory_access(id(shared_value), initial, 'read')
                
                # 模拟处理时间
                time.sleep(0.1)
                
                # 基于旧值的CAS操作
                if shared_value['data'] == initial:
                    shared_value['data'] = 'C'
                    shared_value['count'] += 1
                    self.monitor_memory_access(id(shared_value), 'C', 'cas')
            
            def modifier_thread():
                time.sleep(0.05)
                
                # A -> B
                shared_value['data'] = 'B'
                self.monitor_memory_access(id(shared_value), 'B', 'write')
                
                time.sleep(0.01)
                
                # B -> A (造成ABA)
                shared_value['data'] = 'A'
                self.monitor_memory_access(id(shared_value), 'A', 'write')
            
            return reader_thread, modifier_thread
        
        # 场景2：链表节点的ABA
        def linked_list_aba():
            class Node:
                def __init__(self, value, next=None):
                    self.value = value
                    self.next = next
            
            head = Node('A')
            
            def pop_thread():
                # 尝试移除头节点
                old_head = head
                self.monitor_memory_access(id(head), old_head, 'read')
                
                time.sleep(0.1)  # 模拟延迟
                
                # CAS操作
                if head == old_head:
                    head = old_head.next
                    self.monitor_memory_access(id(head), head, 'cas')
            
            def manipulator_thread():
                time.sleep(0.05)
                
                # 修改链表结构但保持head不变
                original_head = head
                original_next = head.next
                
                # 临时改变
                new_node = Node('B')
                head.next = new_node
                
                time.sleep(0.01)
                
                # 恢复原状（ABA）
                head.next = original_next
                
            return pop_thread, manipulator_thread
        
        return scenarios
```

**答案2：最短违反序列探索器**

```python
class ShortestViolationFinder:
    """找出导致不变量违反的最短执行序列"""
    
    def __init__(self, program, invariant):
        self.program = program
        self.invariant = invariant
        self.shortest_violation = None
        self.explored_sequences = set()
        
    def find_shortest_violation(self):
        """使用BFS找出最短的违反序列"""
        
        from collections import deque
        
        # 初始状态
        initial_state = self.program.get_initial_state()
        queue = deque([(initial_state, [])])  # (state, sequence)
        
        while queue:
            current_state, sequence = queue.popleft()
            
            # 检查不变量
            if not self.invariant(current_state):
                # 找到违反！检查是否是最短的
                if self.shortest_violation is None or len(sequence) < len(self.shortest_violation):
                    self.shortest_violation = sequence
                    print(f"Found violation with length {len(sequence)}")
                continue  # 不再探索这个分支
            
            # 获取所有可能的转换
            transitions = self.get_enabled_transitions(current_state)
            
            for transition in transitions:
                new_state = self.apply_transition(current_state, transition)
                new_sequence = sequence + [transition]
                
                # 剪枝：如果已经比当前最短的长，跳过
                if self.shortest_violation and len(new_sequence) >= len(self.shortest_violation):
                    continue
                
                # 剪枝：如果这个序列已经探索过，跳过
                seq_hash = self.hash_sequence(new_sequence)
                if seq_hash in self.explored_sequences:
                    continue
                
                self.explored_sequences.add(seq_hash)
                queue.append((new_state, new_sequence))
        
        return self.shortest_violation
    
    def minimize_violation_sequence(self, violation_sequence):
        """最小化违反序列，移除不必要的操作"""
        
        # 尝试移除每个操作，看是否仍然违反
        minimized = violation_sequence.copy()
        i = 0
        
        while i < len(minimized):
            # 尝试移除第i个操作
            test_sequence = minimized[:i] + minimized[i+1:]
            
            # 检查是否仍然导致违反
            if self.verify_violation(test_sequence):
                minimized = test_sequence
                # 不增加i，因为列表变短了
            else:
                i += 1
        
        return minimized
```

**答案3：生产者-消费者专用延迟注入**

```python
class ProducerConsumerDelayInjector:
    """针对生产者-消费者模式的延迟注入策略"""
    
    def __init__(self):
        self.buffer_states = {}  # 跟踪缓冲区状态
        self.injection_points = {
            'before_produce': 0.1,
            'after_produce': 0.05,
            'before_consume': 0.15,
            'after_consume': 0.05,
            'buffer_full': 0.3,    # 缓冲区满时注入更多延迟
            'buffer_empty': 0.3    # 缓冲区空时注入更多延迟
        }
        
    def inject_delays(self, queue_operations):
        """包装队列操作以注入延迟"""
        
        def wrapped_put(queue, item):
            # 在生产前注入延迟
            if self.should_inject('before_produce'):
                delay = self.calculate_delay('before_produce', queue)
                time.sleep(delay)
            
            # 如果缓冲区将满，注入额外延迟
            if queue.qsize() >= queue.maxsize - 1:
                if self.should_inject('buffer_full'):
                    time.sleep(self.calculate_delay('buffer_full', queue))
            
            result = queue.put(item)
            
            # 在生产后注入延迟
            if self.should_inject('after_produce'):
                time.sleep(self.calculate_delay('after_produce', queue))
            
            return result
        
        def wrapped_get(queue):
            # 在消费前注入延迟
            if self.should_inject('before_consume'):
                delay = self.calculate_delay('before_consume', queue)
                time.sleep(delay)
            
            # 如果缓冲区将空，注入额外延迟
            if queue.qsize() <= 1:
                if self.should_inject('buffer_empty'):
                    time.sleep(self.calculate_delay('buffer_empty', queue))
            
            result = queue.get()
            
            # 在消费后注入延迟
            if self.should_inject('after_consume'):
                time.sleep(self.calculate_delay('after_consume', queue))
            
            return result
        
        return wrapped_put, wrapped_get
    
    def calculate_delay(self, injection_point, queue):
        """根据队列状态计算延迟"""
        
        base_delay = self.injection_points[injection_point]
        
        # 根据队列填充程度调整
        if queue.maxsize > 0:
            fill_ratio = queue.qsize() / queue.maxsize
            
            if injection_point == 'buffer_full' and fill_ratio > 0.8:
                # 缓冲区快满时增加延迟
                base_delay *= (1 + fill_ratio)
            elif injection_point == 'buffer_empty' and fill_ratio < 0.2:
                # 缓冲区快空时增加延迟
                base_delay *= (2 - fill_ratio)
        
        # 添加随机性
        return base_delay * random.uniform(0.5, 1.5)
    
    def detect_pc_bugs(self):
        """检测常见的生产者-消费者bug"""
        
        detectors = {
            'lost_wakeup': self.detect_lost_wakeup,
            'spurious_wakeup': self.detect_spurious_wakeup,
            'buffer_overflow': self.detect_buffer_overflow,
            'race_condition': self.detect_race_condition
        }
        
        return detectors
```

**进一步练习**：
1. 扩展ABA检测器，使其能够提供修复建议
2. 实现一个可视化工具，展示调度探索的过程
3. 设计一个机器学习模型，根据代码模式预测最佳的延迟注入点

</details>

## 进一步研究

1. **形式化并发模型**：如何使用TLA+、Spin等工具进行并发系统建模？
2. **确定性重放**：如何记录和重放导致并发缺陷的执行？
3. **并发缺陷模式挖掘**：如何从代码库中自动识别常见的并发缺陷模式？
4. **量子计算的并发**：量子并发与经典并发的测试有何不同？
5. **无锁算法测试**：如何有效测试复杂的无锁数据结构？

## 19.3 竞态条件检测技术

### 19.3.1 静态竞态检测

```python
class StaticRaceDetection:
    def lockset_algorithm(self):
        """Lockset算法检测潜在数据竞争"""
        
        class LocksetAnalyzer:
            def __init__(self):
                self.locksets = {}  # 变量 -> 保护它的锁集合
                self.warnings = []
            
            def analyze_access(self, var, accessing_thread, held_locks):
                if var not in self.locksets:
                    # 首次访问，记录锁集
                    self.locksets[var] = set(held_locks)
                else:
                    # 更新锁集为交集
                    self.locksets[var] &= set(held_locks)
                    
                    # 如果锁集为空，可能存在竞态
                    if not self.locksets[var]:
                        self.warnings.append({
                            'variable': var,
                            'thread': accessing_thread,
                            'message': f"Potential race on {var}: no common locks"
                        })
            
            def get_results(self):
                return self.warnings
    
    def escape_analysis(self):
        """逃逸分析识别共享对象"""
        # 分析对象是否可能被多个线程访问
        # 线程局部对象不需要同步
        pass
```

### 19.3.2 动态竞态检测

```python
class DynamicRaceDetection:
    def vector_clock_algorithm(self):
        """使用向量时钟检测happens-before违反"""
        
        class VectorClock:
            def __init__(self, num_threads):
                self.clock = [0] * num_threads
                self.thread_id = None
            
            def increment(self, thread_id):
                """线程执行操作时递增时钟"""
                self.clock[thread_id] += 1
            
            def update(self, other_clock):
                """同步时更新时钟"""
                for i in range(len(self.clock)):
                    self.clock[i] = max(self.clock[i], other_clock[i])
            
            def happens_before(self, other):
                """检查是否存在happens-before关系"""
                return all(self.clock[i] <= other.clock[i] 
                          for i in range(len(self.clock)))
    
    def fasttrack_algorithm(self):
        """FastTrack: 优化的向量时钟算法"""
        # 大多数变量只被少数线程访问
        # 使用epoch（线程ID+时钟）优化
        pass
```

### 19.3.3 预测性竞态检测

```python
class PredictiveRaceDetection:
    def maximal_causal_model(self):
        """从单次执行预测其他可能的竞态"""
        
        class CausalModel:
            def __init__(self, execution_trace):
                self.trace = execution_trace
                self.causal_order = self.build_causal_order()
            
            def build_causal_order(self):
                """构建因果顺序关系"""
                order = {}
                
                for event in self.trace:
                    # 程序顺序
                    if event.thread in order:
                        order[event].add(order[event.thread][-1])
                    
                    # 同步顺序
                    if event.is_synchronization():
                        self.add_sync_order(order, event)
                
                return order
            
            def find_potential_races(self):
                """查找可能在其他调度下发生的竞态"""
                races = []
                
                for e1, e2 in self.get_conflicting_accesses():
                    if not self.must_happen_in_order(e1, e2):
                        races.append((e1, e2))
                
                return races
```

### 练习 19.3

<details>
<summary>点击查看练习</summary>

**问题**：实现一个简化版的happens-before竞态检测器。

**参考答案**：

```python
class SimpleHappensBeforeDetector:
    def __init__(self):
        self.vector_clocks = {}  # thread_id -> VectorClock
        self.lock_clocks = {}    # lock -> VectorClock
        self.var_access = {}     # var -> [(thread, clock, is_write)]
        self.races = []
        
    def on_thread_create(self, parent_id, child_id, num_threads):
        """处理线程创建"""
        # 父线程时钟递增
        self.vector_clocks[parent_id].increment(parent_id)
        
        # 子线程继承父线程时钟
        self.vector_clocks[child_id] = VectorClock(num_threads)
        self.vector_clocks[child_id].update(self.vector_clocks[parent_id])
    
    def on_lock_acquire(self, thread_id, lock):
        """处理锁获取"""
        if lock in self.lock_clocks:
            # 更新线程时钟
            self.vector_clocks[thread_id].update(self.lock_clocks[lock])
        
        self.vector_clocks[thread_id].increment(thread_id)
    
    def on_lock_release(self, thread_id, lock):
        """处理锁释放"""
        self.vector_clocks[thread_id].increment(thread_id)
        
        # 更新锁的时钟
        if lock not in self.lock_clocks:
            self.lock_clocks[lock] = VectorClock(len(self.vector_clocks))
        
        self.lock_clocks[lock].update(self.vector_clocks[thread_id])
    
    def on_memory_access(self, thread_id, var, is_write):
        """处理内存访问"""
        current_clock = self.vector_clocks[thread_id].copy()
        
        if var not in self.var_access:
            self.var_access[var] = []
        
        # 检查与之前访问的竞态
        for prev_thread, prev_clock, prev_is_write in self.var_access[var]:
            if prev_thread != thread_id:  # 不同线程
                if is_write or prev_is_write:  # 至少一个是写
                    # 检查happens-before关系
                    if not (prev_clock.happens_before(current_clock) or
                            current_clock.happens_before(prev_clock)):
                        self.races.append({
                            'var': var,
                            'access1': (prev_thread, 'write' if prev_is_write else 'read'),
                            'access2': (thread_id, 'write' if is_write else 'read'),
                            'message': f"Race on {var} between thread {prev_thread} and {thread_id}"
                        })
        
        # 记录当前访问
        self.var_access[var].append((thread_id, current_clock, is_write))
        self.vector_clocks[thread_id].increment(thread_id)
    
    def get_race_report(self):
        return self.races
```

</details>

## 19.4 死锁检测与预防

### 19.4.1 死锁检测算法

```python
class DeadlockDetection:
    def resource_allocation_graph(self):
        """使用资源分配图检测死锁"""
        
        class RAG:
            def __init__(self):
                self.threads = set()
                self.resources = set()
                self.holds = {}      # thread -> [resources]
                self.waits = {}      # thread -> resource
            
            def add_hold(self, thread, resource):
                if thread not in self.holds:
                    self.holds[thread] = []
                self.holds[thread].append(resource)
            
            def add_wait(self, thread, resource):
                self.waits[thread] = resource
            
            def detect_cycle(self):
                """检测图中是否存在环"""
                visited = set()
                rec_stack = set()
                
                def has_cycle(node, path):
                    visited.add(node)
                    rec_stack.add(node)
                    
                    # 获取后继节点
                    successors = self.get_successors(node)
                    
                    for succ in successors:
                        if succ not in visited:
                            if has_cycle(succ, path + [succ]):
                                return True
                        elif succ in rec_stack:
                            # 找到环
                            cycle_start = path.index(succ)
                            return path[cycle_start:] + [succ]
                    
                    rec_stack.remove(node)
                    return False
                
                # 检查所有节点
                for node in self.threads:
                    if node not in visited:
                        cycle = has_cycle(node, [node])
                        if cycle:
                            return cycle
                
                return None
```

### 19.4.2 死锁预防策略

```python
class DeadlockPrevention:
    def lock_ordering(self):
        """通过锁顺序预防死锁"""
        
        class OrderedLockManager:
            def __init__(self):
                self.lock_order = {}  # lock -> order_number
                self.thread_locks = {}  # thread -> [held_locks]
                self.next_order = 0
            
            def register_lock(self, lock):
                """注册锁并分配顺序号"""
                if lock not in self.lock_order:
                    self.lock_order[lock] = self.next_order
                    self.next_order += 1
            
            def acquire_lock(self, thread_id, lock):
                """按顺序获取锁"""
                if thread_id not in self.thread_locks:
                    self.thread_locks[thread_id] = []
                
                held_locks = self.thread_locks[thread_id]
                
                # 检查锁顺序
                for held in held_locks:
                    if self.lock_order[held] > self.lock_order[lock]:
                        raise Exception(
                            f"Lock order violation: trying to acquire {lock} "
                            f"while holding {held}"
                        )
                
                # 获取锁
                lock.acquire()
                held_locks.append(lock)
    
    def banker_algorithm(self):
        """银行家算法动态避免死锁"""
        # 预分配资源，确保系统始终处于安全状态
        pass
```

### 19.4.3 活锁和饥饿检测

```python
class LivelockStarvationDetection:
    def detect_livelock(self):
        """检测活锁情况"""
        
        class LivelockDetector:
            def __init__(self):
                self.thread_states = {}  # thread -> state_history
                self.progress_counters = {}  # thread -> progress
            
            def monitor_thread_state(self, thread_id, state):
                """监控线程状态变化"""
                if thread_id not in self.thread_states:
                    self.thread_states[thread_id] = []
                
                self.thread_states[thread_id].append({
                    'state': state,
                    'timestamp': time.time()
                })
                
                # 检测重复模式
                if self.detect_repetitive_pattern(thread_id):
                    return "Potential livelock detected"
            
            def detect_repetitive_pattern(self, thread_id):
                """检测状态的重复模式"""
                history = self.thread_states[thread_id]
                
                if len(history) < 10:
                    return False
                
                # 查找重复的状态序列
                recent = history[-10:]
                pattern_length = 3
                
                for i in range(len(recent) - pattern_length * 2):
                    pattern = [s['state'] for s in recent[i:i+pattern_length]]
                    next_pattern = [s['state'] for s in recent[i+pattern_length:i+pattern_length*2]]
                    
                    if pattern == next_pattern:
                        return True
                
                return False
```

### 练习 19.4

<details>
<summary>点击查看练习</summary>

**问题**：设计一个死锁检测和恢复系统。

**参考答案**：

```python
class DeadlockDetectionAndRecovery:
    def __init__(self):
        self.lock_graph = {}  # 资源分配图
        self.checkpoints = {}  # 线程检查点
        self.detection_interval = 1.0  # 检测间隔(秒)
        
    def periodic_detection(self):
        """周期性死锁检测"""
        
        def detection_thread():
            while True:
                time.sleep(self.detection_interval)
                
                # 构建当前的资源分配图
                rag = self.build_resource_allocation_graph()
                
                # 检测死锁
                deadlock_cycle = rag.detect_cycle()
                
                if deadlock_cycle:
                    self.handle_deadlock(deadlock_cycle)
        
        Thread(target=detection_thread, daemon=True).start()
    
    def build_resource_allocation_graph(self):
        """构建资源分配图"""
        rag = ResourceAllocationGraph()
        
        # 收集所有线程的锁持有和等待信息
        for thread in threading.enumerate():
            thread_id = thread.ident
            
            # 获取线程持有的锁
            held_locks = self.get_held_locks(thread_id)
            for lock in held_locks:
                rag.add_hold(thread_id, lock)
            
            # 获取线程等待的锁
            waiting_lock = self.get_waiting_lock(thread_id)
            if waiting_lock:
                rag.add_wait(thread_id, waiting_lock)
        
        return rag
    
    def handle_deadlock(self, cycle):
        """处理检测到的死锁"""
        
        # 策略1: 选择受害者线程
        victim = self.select_victim(cycle)
        
        # 策略2: 回滚或终止
        if self.can_rollback(victim):
            self.rollback_thread(victim)
        else:
            self.terminate_thread(victim)
        
        # 记录死锁信息
        self.log_deadlock(cycle, victim)
    
    def select_victim(self, cycle):
        """选择要终止的受害者线程"""
        
        # 考虑因素：
        # 1. 线程优先级
        # 2. 已完成的工作量
        # 3. 持有的资源数量
        # 4. 剩余的工作量
        
        scores = {}
        for thread in cycle:
            scores[thread] = self.calculate_victim_score(thread)
        
        # 选择得分最低的作为受害者
        return min(scores, key=scores.get)
    
    def calculate_victim_score(self, thread):
        """计算线程作为受害者的得分"""
        score = 0
        
        # 优先级越高，得分越高（越不容易被选为受害者）
        score += self.get_thread_priority(thread) * 10
        
        # 已完成工作越多，得分越高
        score += self.get_completed_work(thread)
        
        # 持有资源越少，得分越低（更容易被选中）
        score -= len(self.get_held_locks(thread)) * 5
        
        return score
    
    def rollback_thread(self, thread_id):
        """回滚线程到检查点"""
        if thread_id in self.checkpoints:
            checkpoint = self.checkpoints[thread_id]
            # 恢复线程状态
            self.restore_thread_state(thread_id, checkpoint)
            # 释放所有锁
            self.release_all_locks(thread_id)
            # 重新调度线程
            self.reschedule_thread(thread_id)
```

</details>

## 进一步研究

1. **分布式系统的死锁检测**：如何在分布式环境中检测全局死锁？
2. **GPU并发测试**：如何测试CUDA/OpenCL程序的并发正确性？
3. **事务内存测试**：软件事务内存(STM)的测试策略是什么？
4. **确定性并发测试**：如何实现确定性的并发测试框架？
5. **机器学习辅助的并发测试**：如何使用ML技术预测并发缺陷？

## 19.5 并发测试工具与实践

### 19.5.1 动态分析工具

```python
class ConcurrencyTestingTools:
    def thread_sanitizer(self):
        """ThreadSanitizer (TSan) 特性"""
        return {
            "功能": [
                "数据竞争检测",
                "死锁检测",
                "happens-before关系跟踪",
                "低运行时开销(5-15x)"
            ],
            "使用方式": "编译时添加 -fsanitize=thread",
            "优势": "精确的竞态检测，低误报率",
            "限制": "需要重新编译，内存开销较大"
        }
    
    def helgrind_usage(self):
        """Valgrind Helgrind 工具"""
        # 检测POSIX线程错误
        # 不需要重新编译
        # 运行时开销较大(20-50x)
        pass
    
    def intel_inspector(self):
        """Intel Inspector 特性"""
        # 商业工具，功能全面
        # 支持死锁、数据竞争、内存错误
        # 提供可视化界面
        pass
```

### 19.5.2 模型检测工具

```python
class ModelCheckingTools:
    def java_pathfinder(self):
        """JPF: Java程序的模型检测"""
        return {
            "原理": "系统化探索所有可能的执行路径",
            "特性": [
                "自定义调度策略",
                "状态空间缩减",
                "属性验证",
                "反例生成"
            ],
            "应用": "关键系统的正确性验证"
        }
    
    def spin_model_checker(self):
        """SPIN: 并发系统协议验证"""
        # 使用Promela建模语言
        # LTL属性规范
        # 高效的状态空间探索
        pass
    
    def tla_plus(self):
        """TLA+: 并发算法规范和验证"""
        # 数学化的规范语言
        # 不变量和时序属性
        # 适合复杂分布式算法
        pass
```

### 19.5.3 测试框架集成

```python
class ConcurrencyTestFramework:
    def design_test_harness(self):
        """设计并发测试框架"""
        
        class ConcurrentTestRunner:
            def __init__(self):
                self.test_cases = []
                self.schedulers = []
                self.detectors = []
            
            def add_test(self, test_func, num_threads, iterations):
                """添加并发测试用例"""
                self.test_cases.append({
                    'function': test_func,
                    'threads': num_threads,
                    'iterations': iterations,
                    'invariants': []
                })
            
            def add_invariant(self, test_name, invariant_func):
                """添加不变量检查"""
                # 在测试执行期间持续检查
                pass
            
            def run_with_stress(self):
                """压力测试模式"""
                for test in self.test_cases:
                    # 增加线程数
                    # 注入延迟
                    # 随机调度
                    self.execute_stressed_test(test)
            
            def run_with_schedule_exploration(self):
                """调度探索模式"""
                for test in self.test_cases:
                    # 系统化探索不同调度
                    schedules = self.generate_schedules(test)
                    for schedule in schedules:
                        self.execute_with_schedule(test, schedule)
```

### 19.5.4 实践案例：测试并发队列

```python
class ConcurrentQueueTesting:
    def test_concurrent_queue(self):
        """全面测试并发队列实现"""
        
        class QueueTestSuite:
            def __init__(self, queue_impl):
                self.queue = queue_impl
                self.results = []
            
            def test_basic_safety(self):
                """基本安全性测试"""
                
                def producer(queue, items):
                    for item in items:
                        queue.enqueue(item)
                
                def consumer(queue, count):
                    consumed = []
                    for _ in range(count):
                        item = queue.dequeue()
                        if item is not None:
                            consumed.append(item)
                    return consumed
                
                # 测试：生产的所有元素都被消费
                total_items = 1000
                num_producers = 4
                num_consumers = 4
                
                # 验证没有元素丢失或重复
                self.verify_no_lost_items()
                self.verify_no_duplicates()
            
            def test_linearizability(self):
                """线性化测试"""
                
                # 记录所有操作的开始和结束时间
                operations = []
                
                def record_operation(op_type, value, start_time, end_time):
                    operations.append({
                        'type': op_type,
                        'value': value,
                        'start': start_time,
                        'end': end_time
                    })
                
                # 检查是否存在合法的线性化
                return self.check_linearizability(operations)
            
            def test_progress_properties(self):
                """进展性测试"""
                
                # 测试无锁性
                def test_lock_freedom():
                    # 确保系统级进展
                    pass
                
                # 测试无等待性
                def test_wait_freedom():
                    # 确保每个操作在有限步内完成
                    pass
            
            def stress_test_with_monitoring(self):
                """带监控的压力测试"""
                
                monitor = PerformanceMonitor()
                
                # 监控指标
                monitor.track("throughput")
                monitor.track("latency")
                monitor.track("contention")
                
                # 运行高并发测试
                self.run_high_concurrency_test()
                
                # 分析性能退化
                return monitor.analyze_degradation()
```

### 练习 19.5

<details>
<summary>点击查看练习</summary>

**问题**：设计一个测试套件来验证读写锁的正确性。

**参考答案**：

```python
class ReadWriteLockTestSuite:
    def __init__(self, rwlock_impl):
        self.rwlock = rwlock_impl
        self.shared_data = 0
        self.read_count = 0
        self.write_count = 0
        
    def test_mutual_exclusion(self):
        """测试写者之间的互斥"""
        
        conflicts = []
        writing = threading.Event()
        
        def writer(thread_id):
            for i in range(100):
                self.rwlock.write_lock()
                
                # 检查是否有其他写者
                if writing.is_set():
                    conflicts.append(f"Writer conflict: thread {thread_id}")
                
                writing.set()
                
                # 模拟写操作
                old_value = self.shared_data
                time.sleep(0.001)  # 增加冲突机会
                self.shared_data = old_value + 1
                
                writing.clear()
                self.rwlock.write_unlock()
        
        # 启动多个写者
        threads = [Thread(target=writer, args=(i,)) for i in range(5)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        
        assert len(conflicts) == 0, f"Found conflicts: {conflicts}"
        assert self.shared_data == 500, f"Expected 500, got {self.shared_data}"
    
    def test_reader_writer_exclusion(self):
        """测试读者和写者的互斥"""
        
        violations = []
        
        def reader(thread_id):
            for _ in range(100):
                self.rwlock.read_lock()
                
                # 读取时记录值
                value_at_start = self.shared_data
                time.sleep(0.001)
                value_at_end = self.shared_data
                
                # 检查读取期间值是否改变
                if value_at_start != value_at_end:
                    violations.append(
                        f"Read inconsistency in thread {thread_id}: "
                        f"{value_at_start} -> {value_at_end}"
                    )
                
                self.rwlock.read_unlock()
        
        def writer(thread_id):
            for _ in range(50):
                self.rwlock.write_lock()
                self.shared_data += 1
                self.rwlock.write_unlock()
                time.sleep(0.001)
        
        # 混合读者和写者
        threads = []
        threads.extend([Thread(target=reader, args=(i,)) for i in range(3)])
        threads.extend([Thread(target=writer, args=(i,)) for i in range(2)])
        
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        
        assert len(violations) == 0, f"Found violations: {violations}"
    
    def test_reader_parallelism(self):
        """测试多个读者可以并发"""
        
        max_concurrent_readers = 0
        current_readers = 0
        reader_lock = threading.Lock()
        
        def reader(thread_id):
            nonlocal max_concurrent_readers, current_readers
            
            self.rwlock.read_lock()
            
            with reader_lock:
                current_readers += 1
                max_concurrent_readers = max(max_concurrent_readers, current_readers)
            
            time.sleep(0.01)  # 保持读锁一段时间
            
            with reader_lock:
                current_readers -= 1
            
            self.rwlock.read_unlock()
        
        # 启动多个读者
        threads = [Thread(target=reader, args=(i,)) for i in range(10)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        
        # 应该观察到多个读者并发
        assert max_concurrent_readers > 1, \
            f"Expected concurrent readers, but max was {max_concurrent_readers}"
    
    def test_fairness(self):
        """测试公平性：避免写者饥饿"""
        
        write_timestamps = []
        
        def writer(thread_id):
            start_time = time.time()
            self.rwlock.write_lock()
            acquired_time = time.time()
            
            write_timestamps.append({
                'thread': thread_id,
                'wait_time': acquired_time - start_time
            })
            
            time.sleep(0.001)
            self.rwlock.write_unlock()
        
        def reader(thread_id):
            for _ in range(50):
                self.rwlock.read_lock()
                time.sleep(0.0001)  # 短暂持有
                self.rwlock.read_unlock()
        
        # 先启动读者制造负载
        reader_threads = [Thread(target=reader, args=(i,)) for i in range(5)]
        for t in reader_threads:
            t.start()
        
        time.sleep(0.01)  # 让读者先运行
        
        # 启动写者
        writer_threads = [Thread(target=writer, args=(i,)) for i in range(3)]
        for t in writer_threads:
            t.start()
        
        # 等待完成
        for t in reader_threads + writer_threads:
            t.join()
        
        # 检查写者等待时间
        max_wait = max(ts['wait_time'] for ts in write_timestamps)
        assert max_wait < 1.0, f"Writer starvation detected: max wait {max_wait}s"
```

</details>

## 19.6 高级并发测试技术

### 19.6.1 确定性测试

```python
class DeterministicConcurrencyTesting:
    def deterministic_scheduler(self):
        """实现确定性调度器"""
        
        class DeterministicScheduler:
            def __init__(self, seed=42):
                self.random = Random(seed)
                self.threads = []
                self.current_thread = None
                self.decision_points = []
            
            def register_thread(self, thread):
                """注册线程到调度器"""
                self.threads.append(thread)
            
            def schedule_next(self):
                """确定性地选择下一个线程"""
                # 基于种子的伪随机选择
                next_thread = self.random.choice(self.threads)
                self.switch_to(next_thread)
            
            def record_execution(self):
                """记录执行序列用于重放"""
                return {
                    'seed': self.random.seed,
                    'decisions': self.decision_points,
                    'thread_order': [t.id for t in self.threads]
                }
            
            def replay_execution(self, record):
                """重放之前的执行"""
                self.random = Random(record['seed'])
                self.decision_points = record['decisions']
                # 按记录的顺序执行
```

### 19.6.2 并发覆盖准则

```python
class ConcurrencyCoverage:
    def coverage_criteria(self):
        """并发测试覆盖准则"""
        
        return {
            "同步覆盖": "覆盖所有同步原语的使用",
            "交错覆盖": "覆盖关键语句的不同交错",
            "通信覆盖": "覆盖线程间的通信模式",
            "延迟覆盖": "在不同延迟条件下测试"
        }
    
    def measure_interleaving_coverage(self):
        """度量交错覆盖率"""
        
        class InterleavingCoverage:
            def __init__(self):
                self.covered_interleavings = set()
                self.potential_interleavings = set()
            
            def identify_racing_pairs(self, program):
                """识别可能竞争的语句对"""
                pairs = []
                for stmt1 in program.statements:
                    for stmt2 in program.statements:
                        if self.may_race(stmt1, stmt2):
                            pairs.append((stmt1, stmt2))
                return pairs
            
            def compute_coverage(self):
                """计算覆盖率"""
                if not self.potential_interleavings:
                    return 1.0
                
                return len(self.covered_interleavings) / len(self.potential_interleavings)
```

### 19.6.3 混沌工程

```python
class ChaosConcurrencyTesting:
    def chaos_injection(self):
        """注入混沌到并发系统"""
        
        class ChaosInjector:
            def __init__(self):
                self.injection_points = [
                    "线程调度",
                    "锁获取延迟",
                    "网络延迟",
                    "CPU亲和性",
                    "内存压力"
                ]
            
            def inject_scheduling_chaos(self):
                """随机改变线程优先级"""
                for thread in active_threads():
                    if random.random() < 0.1:
                        # 随机改变优先级
                        new_priority = random.choice(['LOW', 'NORMAL', 'HIGH'])
                        thread.set_priority(new_priority)
            
            def inject_timing_chaos(self):
                """注入时间相关的混沌"""
                # 随机睡眠
                if random.random() < 0.05:
                    time.sleep(random.uniform(0, 0.1))
                
                # CPU亲和性变化
                if random.random() < 0.02:
                    current_cpu = get_current_cpu()
                    new_cpu = (current_cpu + 1) % cpu_count()
                    set_cpu_affinity(new_cpu)
```

## 进一步研究

1. **形式化并发测试**：如何将形式化方法与实际测试结合？
2. **量子并发**：量子计算中的并发测试有何特殊性？
3. **AI辅助的并发测试**：如何用机器学习改进测试用例生成？
4. **云原生并发测试**：如何测试容器化和微服务架构中的并发？
5. **硬件并发测试**：如何测试硬件级别的内存模型和缓存一致性？

## 本章小结

并发测试是确保多线程和分布式系统正确性的关键技术。本章系统介绍了：

1. 并发缺陷的本质和分类
2. 竞态条件的检测技术
3. 死锁的预防和检测方法
4. 实用的测试工具和框架
5. 高级测试技术如确定性测试和混沌工程

有效的并发测试需要结合多种技术：静态分析发现潜在问题，动态检测捕获运行时错误，系统化探索覆盖不同的执行路径。随着并发系统的复杂度增加，并发测试技术也在不断演进。

下一章，我们将探讨分布式系统测试，研究如何在网络分区、消息延迟等复杂条件下确保系统的正确性。