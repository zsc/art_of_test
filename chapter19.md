# 第19章：并发测试

并发程序的正确性是软件工程中最具挑战性的问题之一。竞态条件、死锁、活锁等并发缺陷难以重现和调试。本章将系统介绍并发测试的理论基础、实用技术和工具支持。

## 19.1 并发缺陷的本质

### 19.1.1 并发缺陷分类

1. **竞态条件（Race Condition）**
   - 数据竞争：多个线程同时访问共享数据
   - 顺序违反：操作顺序依赖被破坏
   - 原子性违反：应该原子执行的操作被中断

2. **死锁（Deadlock）**
   - 循环等待资源
   - 持有并等待
   - 不可剥夺
   - 互斥访问

3. **活锁（Livelock）**
   - 线程持续活动但无进展
   - 过度礼让导致的问题

4. **饥饿（Starvation）**
   - 某些线程长期得不到资源
   - 不公平的调度策略

### 19.1.2 并发测试的挑战

```python
class ConcurrencyTestingChallenges:
    def why_concurrent_bugs_are_hard(self):
        return {
            "非确定性": "相同输入可能产生不同结果",
            "调度敏感": "错误依赖特定的线程调度",
            "海森堡效应": "观测行为改变程序执行",
            "状态空间爆炸": "可能的交错执行数量指数增长",
            "硬件依赖": "不同硬件表现不同"
        }
    
    def demonstrate_nondeterminism(self):
        # 简单的竞态条件示例
        counter = 0
        
        def increment():
            global counter
            temp = counter
            # 在这里可能发生上下文切换
            counter = temp + 1
        
        # 多次运行可能得到不同结果
        # 期望: counter = 2
        # 实际: counter 可能是 1 或 2
```

### 19.1.3 happens-before关系

理解并发的关键是happens-before关系：

```python
class HappensBeforeRelation:
    def basic_rules(self):
        return [
            "程序顺序规则：同一线程内的操作按程序顺序",
            "锁规则：unlock happens-before 后续的lock",
            "volatile规则：写volatile happens-before 读",
            "线程启动规则：start() happens-before 线程内操作",
            "线程终止规则：线程内操作 happens-before join()返回"
        ]
    
    def transitivity(self):
        # 如果 A happens-before B 且 B happens-before C
        # 则 A happens-before C
        pass
```

### 练习 19.1

<details>
<summary>点击查看练习</summary>

**问题**：分析以下代码的潜在并发问题：

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

**参考答案**：

1. **数据竞争**：balance的读写没有同步保护
   - deposit和withdraw中的`balance = balance + amount`不是原子操作
   
2. **原子性违反**：transfer方法应该是原子的
   - withdraw和deposit之间可能被中断
   - 可能导致钱"消失"或"凭空产生"

3. **条件竞争**：withdraw中的检查-执行模式
   - 在检查余额和扣款之间，余额可能被其他线程修改
   
4. **潜在死锁**：如果两个账户互相转账
   - A转给B的同时B转给A，可能死锁（需要按顺序获取锁）

修复方案：使用synchronized或ReentrantLock保护所有方法，transfer中按账户ID顺序获取锁避免死锁。

</details>

## 19.2 系统化的并发测试方法

### 19.2.1 压力测试

通过增加并发度来暴露问题：

```python
class StressTesting:
    def design_stress_test(self, target_function, shared_resource):
        """设计压力测试暴露并发问题"""
        
        def stress_test_framework():
            num_threads = cpu_count() * 4  # 超额订阅
            iterations = 10000
            
            # 1. 预热阶段
            warmup_threads(target_function)
            
            # 2. 施加压力
            results = []
            for _ in range(iterations):
                threads = [
                    Thread(target=target_function, args=(shared_resource,))
                    for _ in range(num_threads)
                ]
                
                # 使用屏障同步启动
                barrier = Barrier(num_threads)
                
                # 启动所有线程
                for t in threads:
                    t.start()
                
                # 等待完成
                for t in threads:
                    t.join()
                
                # 验证不变量
                if not check_invariants(shared_resource):
                    results.append("Invariant violation detected")
            
            return results
```

### 19.2.2 调度探索

主动探索不同的线程交错：

```python
class ScheduleExploration:
    def systematic_exploration(self):
        """系统化探索可能的调度"""
        
        class ScheduleController:
            def __init__(self):
                self.decision_points = []
                self.explored_schedules = set()
            
            def at_decision_point(self, thread_id, choices):
                """在调度决策点记录和控制"""
                point = (thread_id, tuple(choices))
                self.decision_points.append(point)
                
                # 选择下一个要执行的线程
                return self.make_scheduling_decision(choices)
            
            def explore_all_schedules(self):
                """深度优先搜索所有可能的调度"""
                # 使用回溯算法探索调度空间
                pass
    
    def partial_order_reduction(self):
        """减少需要探索的调度数量"""
        # 识别独立的操作
        # 只探索具有不同结果的调度
        pass
```

### 19.2.3 延迟注入

通过注入延迟来增加交错概率：

```python
class DelayInjection:
    def inject_delays(self, program):
        """在关键位置注入随机延迟"""
        
        injection_points = [
            "获取锁之前",
            "释放锁之后",
            "读共享变量之前",
            "写共享变量之后"
        ]
        
        def instrumented_operation(original_op):
            def wrapper(*args, **kwargs):
                if should_inject_delay():
                    sleep(random.uniform(0, 0.01))  # 0-10ms延迟
                
                result = original_op(*args, **kwargs)
                
                if should_inject_delay():
                    sleep(random.uniform(0, 0.01))
                
                return result
            return wrapper
        
        return instrumented_operation
```

### 练习 19.2

<details>
<summary>点击查看练习</summary>

**问题**：设计一个测试框架来检测ABA问题。

**参考答案**：

```python
class ABADetector:
    """检测ABA问题的测试框架"""
    
    def __init__(self):
        self.value_history = {}  # 记录每个地址的值历史
        self.access_log = []      # 记录所有访问
    
    def monitor_cas_operation(self, address, expected, new_value):
        """监控CAS操作检测ABA"""
        
        # 记录访问
        thread_id = current_thread().ident
        timestamp = time.time()
        
        self.access_log.append({
            'thread': thread_id,
            'time': timestamp,
            'address': address,
            'operation': 'CAS',
            'expected': expected,
            'new': new_value
        })
        
        # 检查值历史
        if address in self.value_history:
            history = self.value_history[address]
            
            # 检测ABA模式：A -> B -> A
            if len(history) >= 3:
                if (history[-3]['value'] == expected and
                    history[-2]['value'] != expected and
                    history[-1]['value'] == expected):
                    
                    return {
                        'aba_detected': True,
                        'pattern': history[-3:],
                        'message': f"ABA detected at {address}: {history[-3]['value']} -> {history[-2]['value']} -> {history[-1]['value']}"
                    }
        
        # 更新历史
        if address not in self.value_history:
            self.value_history[address] = []
        
        self.value_history[address].append({
            'value': new_value,
            'thread': thread_id,
            'time': timestamp
        })
        
        return {'aba_detected': False}
    
    def create_aba_test(self):
        """创建一个故意触发ABA的测试"""
        
        shared_ptr = AtomicPointer(initial_value='A')
        aba_detected = False
        
        def thread1():
            # 读取值A
            old_value = shared_ptr.get()  # 'A'
            
            # 模拟长时间操作
            sleep(0.1)
            
            # CAS操作，期望值仍是A
            success = shared_ptr.compare_and_swap(old_value, 'C')
            
            if success and self.monitor_cas_operation(
                id(shared_ptr), old_value, 'C')['aba_detected']:
                nonlocal aba_detected
                aba_detected = True
        
        def thread2():
            # 快速执行 A -> B -> A
            sleep(0.05)
            shared_ptr.set('B')
            sleep(0.01)
            shared_ptr.set('A')
        
        # 运行测试
        t1 = Thread(target=thread1)
        t2 = Thread(target=thread2)
        
        t1.start()
        t2.start()
        
        t1.join()
        t2.join()
        
        return aba_detected
```

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