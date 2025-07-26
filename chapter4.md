# 第4章：单元测试

单元测试是软件测试金字塔的基础，它验证代码的最小可测试单元。本章深入探讨单元测试的原理、实践和高级技术，展示如何通过良好的单元测试构建可靠的软件系统。

## 4.1 测试驱动开发（TDD）

测试驱动开发不仅是一种测试技术，更是一种设计方法论。它通过"测试先行"的方式引导软件设计，产生更模块化、可测试的代码。

### 4.1.1 TDD的核心循环

TDD遵循严格的"红-绿-重构"循环：

```
┌─────────────┐
│   写测试    │ ──→ 红：测试失败
└─────────────┘
      ↑                    ↓
      │              ┌─────────────┐
      │              │  写代码     │ ──→ 绿：测试通过
      │              └─────────────┘
      │                    ↓
┌─────────────┐      ┌─────────────┐
│   重复      │ ←──  │   重构      │ ──→ 绿：测试仍通过
└─────────────┘      └─────────────┘
```

**关键原则**：
1. 只写刚好让测试失败的代码
2. 只写刚好让测试通过的生产代码
3. 只在测试通过时重构

### 4.1.2 TDD的深层价值

1. **设计驱动**
   - 强迫思考接口而非实现
   - 产生低耦合、高内聚的设计
   - 自然产生依赖注入点

2. **即时反馈**
   - 立即知道代码是否工作
   - 小步前进，降低认知负担
   - 容易定位问题

3. **活文档**
   - 测试描述了代码的行为
   - 示例驱动的规范
   - 永远与代码同步

4. **重构信心**
   - 完整的测试网提供安全保障
   - 鼓励持续改进代码
   - 降低技术债务

### 4.1.3 TDD实践示例

让我们通过实现一个栈来展示TDD过程：

**第一个测试：空栈**
编写测试：test_new_stack_is_empty() → 断言新栈为空

**最小实现**
创建Stack类，is_empty()方法直接返回True

**第二个测试：压栈后不为空**
编写测试：压栈后调用is_empty()应返回False

**扩展实现**
- 添加内部存储结构
- is_empty()基于存储结构判断
- 实现push()方法

通过这种小步迭代，逐步构建完整功能，每一步都有测试保护。

### 4.1.4 TDD的常见误区

1. **测试过度具体**
   - 错误：测试内部实现细节（如检查是否使用list存储）
   - 正确：测试外部可观察行为（如LIFO顺序）

2. **大步跳跃**
   - 一次写太多测试
   - 一次实现太多功能
   - 跳过重构步骤

3. **忽视测试质量**
   - 测试代码也需要维护
   - 避免重复和耦合
   - 保持测试简单清晰

### 4.1.5 TDD的适用性

**适合TDD的场景**：
- 算法实现
- 业务规则
- 数据转换
- API设计

**TDD困难的场景**：
- UI交互
- 并发代码
- 性能优化
- 探索性编程

### 练习 4.1

1. 使用TDD实现一个简单的计算器，支持加减乘除和括号。记录你的测试顺序。

<details>
<summary>参考答案</summary>

TDD实现计算器的测试顺序：

1. 最简单的情况 - 单个数字：calculate("5") = 5
2. 加法：calculate("2+3") = 5
3. 减法：calculate("5-3") = 2
4. 连续运算：calculate("2+3-1") = 4
5. 乘法（优先级）：calculate("2+3*4") = 14
6. 除法：calculate("10/2") = 5
7. 括号：calculate("(2+3)*4") = 20
8. 嵌套括号：calculate("((2+3)*4+5)*2") = 50
9. 错误处理：除零抛出异常
10. 空格处理：忽略表达式中的空格

实现要点：
- 每次只实现让当前测试通过的最小代码
- 在绿色状态下重构（如提取方法）
- 逐步处理复杂性（优先级、括号等）
</details>

2. 分析为什么GUI测试难以应用TDD？提出可能的解决方案。

<details>
<summary>参考答案</summary>

GUI测试TDD困难的原因：

1. **反馈循环慢**
   - GUI需要渲染
   - 事件处理异步
   - 测试执行慢

2. **定义"失败"困难**
   - 视觉效果难以断言
   - 布局的"正确性"主观
   - 跨平台差异

3. **测试脆弱**
   - 小改动导致大量测试失败
   - 定位元素困难
   - 时序问题

解决方案：

1. **架构分离**
   ```
   展示层（薄）
       ↓
   展示逻辑层（可TDD）
       ↓
   业务逻辑层（可TDD）
   ```

2. **视觉TDD变体**
   - 截图对比测试
   - 组件级TDD
   - Storybook驱动开发

3. **行为驱动开发（BDD）**
   ```gherkin
   Given 用户在登录页面
   When 输入正确的用户名密码
   Then 应该跳转到主页
   ```

4. **测试金字塔调整**
   - 更多单元测试逻辑
   - 少量集成测试
   - 最少E2E测试

5. **工具支持**
   - 可视化测试工具
   - 组件测试框架
   - 快速反馈机制
</details>

### 进一步研究

- TDD与类型系统：强类型语言中TDD的价值是否降低？
- 自动化TDD：能否自动生成下一个应该写的测试？
- TDD度量：如何量化TDD对代码质量的影响？
- 反向TDD：从代码生成测试，然后删除代码重新TDD？
- TDD与形式化方法：如何结合TDD和形式化规范？
- 并发TDD：如何为并发代码设计TDD流程？

## 4.2 Mock、Stub和测试替身

单元测试的核心挑战是隔离——如何测试一个依赖于外部系统的单元？测试替身（Test Doubles）提供了解决方案。

### 4.2.1 测试替身分类

Gerard Meszaros定义了五种测试替身：

1. **Dummy** - 占位符
   - 传递但不使用
   - 满足参数列表要求
   ```python
   def test_process_with_logger():
       dummy_logger = None  # 不会被使用
       processor = Processor(dummy_logger)
       assert processor.process_simple() == 42
   ```

2. **Stub** - 返回预定响应
   - 提供固定返回值
   - 不验证调用
   ```python
   class StubUserRepository:
       def find_by_id(self, id):
           return User(id=id, name="Test User")
   ```

3. **Spy** - 记录调用信息
   - 记录被调用情况
   - 可以验证交互
   ```python
   class SpyEmailService:
       def __init__(self):
           self.sent_emails = []
       
       def send(self, to, subject, body):
           self.sent_emails.append((to, subject, body))
   ```

4. **Mock** - 预设期望
   - 预定义期望的调用
   - 自动验证交互
   ```python
   mock_payment = Mock()
   mock_payment.charge.return_value = True
   mock_payment.charge.assert_called_once_with(100, "USD")
   ```

5. **Fake** - 简化实现
   - 工作的简化版本
   - 不适合生产环境
   ```python
   class FakeDatabase:
       def __init__(self):
           self.data = {}
       
       def save(self, key, value):
           self.data[key] = value
       
       def get(self, key):
           return self.data.get(key)
   ```

### 4.2.2 选择合适的测试替身

```
需要验证交互？
    是 → Mock或Spy
    否 → 需要特定行为？
         是 → Stub或Fake
         否 → Dummy
```

### 4.2.3 Mock的正确使用

**好的Mock使用**：
```python
def test_order_processing_sends_email():
    # Arrange
    email_service = Mock()
    order_processor = OrderProcessor(email_service)
    order = Order(id=123, customer_email="test@example.com")
    
    # Act
    order_processor.process(order)
    
    # Assert
    email_service.send_confirmation.assert_called_once_with(
        to="test@example.com",
        order_id=123
    )
```

**过度Mock的陷阱**：
```python
# 糟糕：测试实现而非行为
def test_bad_mocking():
    calculator = Mock()
    calculator.add.return_value = 5
    
    # 这个测试毫无意义
    assert calculator.add(2, 3) == 5
```

### 4.2.4 测试替身的设计原则

1. **最小化Mock**
   - 只mock不能控制的部分
   - 优先使用真实对象
   - 考虑使用Fake而非Mock

2. **接口稳定性**
   - Mock稳定的接口
   - 避免mock易变的实现细节
   - 使用明确的协议/接口

3. **行为验证 vs 状态验证**
   ```python
   # 状态验证（优先）
   def test_adds_item_to_inventory():
       inventory = Inventory()
       inventory.add_item("widget", 5)
       assert inventory.get_quantity("widget") == 5
   
   # 行为验证（必要时）
   def test_logs_security_event():
       logger = Mock()
       security = SecurityManager(logger)
       security.detect_intrusion()
       logger.log.assert_called_with(severity="HIGH", event="intrusion")
   ```

### 4.2.5 高级Mock技术

1. **部分Mock（Partial Mocking）**
   ```python
   class DatabaseService:
       def connect(self):
           # 复杂的连接逻辑
           pass
       
       def query(self, sql):
           # 需要mock的方法
           pass
   
   # 只mock特定方法
   service = DatabaseService()
   with patch.object(service, 'query', return_value=[]):
       result = service.fetch_users()  # 使用真实connect，mock的query
   ```

2. **条件Mock**
   ```python
   def side_effect_function(arg):
       if arg == "special":
           raise ValueError("Special case")
       return f"processed_{arg}"
   
   mock_func.side_effect = side_effect_function
   ```

3. **Mock链**
   ```python
   # 支持链式调用
   mock = Mock()
   mock.method1.return_value.method2.return_value = "result"
   assert mock.method1().method2() == "result"
   ```

### 4.2.6 测试替身的代价

1. **耦合到实现**
   - Mock测试可能过于脆弱
   - 重构困难
   - 假阳性测试

2. **维护负担**
   - 保持Mock与真实对象同步
   - 复杂的setup代码
   - 测试可读性下降

3. **虚假信心**
   - 测试通过但集成失败
   - Mock行为与真实不符
   - 隐藏的集成问题

### 练习 4.2

1. 设计一个用户服务的测试策略，它依赖于数据库、缓存和邮件服务。说明每个依赖使用什么类型的测试替身。

<details>
<summary>参考答案</summary>

用户服务测试策略：

**系统结构**：UserService依赖于数据库、缓存和邮件服务

**测试替身选择**：

1. **数据库 - 使用Fake**
   - 内存实现，保持事务语义
   - 支持基本的CRUD操作
   - 可以模拟事务失败等情况
   - 选择理由：需要复杂的事务语义，Mock难以维护

2. **缓存 - 使用Stub**
   - 简单的键值存储
   - 不需要实现TTL等复杂特性
   - 总是返回预设的值
   - 选择理由：行为简单可预测，不需要验证交互

3. **邮件服务 - 使用Spy**
   - 记录所有发送的邮件
   - 提供验证方法
   - 不真正发送邮件
   - 选择理由：需要验证邮件是否被发送和内容

**测试示例流程**：
1. 创建测试替身
2. 注册用户
3. 验证数据库保存
4. 验证缓存更新
5. 验证邮件发送

**关键点**：
- 每个依赖使用最适合的测试替身类型
- Fake提供最接近真实的行为
- Spy用于需要验证的交互
- Stub用于简单的返回值
</details>

2. 识别以下测试代码的问题，并提出改进方案：
```python
问题代码分析：
# 创建5个Mock对象
# 所有依赖都是Mock
# 设置多个返回值
# 验证所有方法调用
```

<details>
<summary>参考答案</summary>

问题识别：

1. **过度Mock**：所有依赖都被Mock
2. **脆弱测试**：与实现紧密耦合
3. **低可读性**：大量setup代码
4. **低信心**：没有测试真实集成

改进方案：

```python
# 1. 使用Builder模式减少setup
class OrderServiceBuilder:
    def __init__(self):
        self.db = FakeOrderDatabase()
        self.payment = StubPaymentGateway(always_succeed=True)
        self.inventory = FakeInventory({"item1": 10})
        self.shipping = StubShippingCalculator(flat_rate=10)
        self.logger = DummyLogger()
    
    def with_payment_failure(self):
        self.payment = StubPaymentGateway(always_succeed=False)
        return self
    
    def build(self):
        return OrderService(
            self.db, self.logger, self.payment,
            self.inventory, self.shipping
        )

# 2. 使用真实对象的简化版本
class FakeOrderDatabase:
    def __init__(self):
        self.orders = {
            1: Order(id=1, items=[{"id": "item1", "quantity": 2}])
        }
    
    def get_order(self, order_id):
        return self.orders.get(order_id)
    
    def update_order_status(self, order_id, status):
        if order_id in self.orders:
            self.orders[order_id].status = status

# 3. 专注于行为而非实现
def test_successful_order_processing():
    # Arrange
    service = OrderServiceBuilder().build()
    
    # Act
    result = service.process_order(1)
    
    # Assert
    assert result.status == "SUCCESS"
    assert result.shipping_cost == 10
    # 验证副作用而非调用
    order = service.db.get_order(1)
    assert order.status == "PROCESSED"

# 4. 分离关注点的测试
def test_payment_failure_handling():
    # 只关注支付失败的处理
    service = OrderServiceBuilder()\
        .with_payment_failure()\
        .build()
    
    result = service.process_order(1)
    
    assert result.status == "PAYMENT_FAILED"
    # 不需要验证所有的Mock调用

# 5. 集成测试补充
def test_order_processing_integration():
    # 使用更真实的组件
    service = OrderService(
        db=TestDatabase(),  # 测试数据库
        logger=ConsoleLogger(),
        payment=TestPaymentGateway(),  # 测试环境网关
        inventory=FakeInventory({"item1": 10}),
        shipping=RealShippingCalculator()
    )
    
    # 端到端测试流程
    result = service.process_order(1)
    assert result.status == "SUCCESS"


**关键改进点**：
1. 减少Mock数量
2. 使用合适的测试替身类型
3. 提高测试可读性
4. 关注行为而非实现
5. 分层测试策略
</details>

### 进一步研究

- 自动Mock生成：能否从接口定义自动生成合适的测试替身？
- Mock验证策略：如何自动验证Mock的行为与真实对象一致？
- 测试替身的性能影响：使用测试替身对测试执行时间的影响如何量化？
- Contract Testing：如何确保测试替身与真实服务的契约一致？
- Mock的可视化：如何可视化复杂的Mock交互以提高理解？
- 智能测试替身：使用机器学习创建更真实的测试替身？

## 4.3 参数化测试

参数化测试让我们能够用多组数据运行同一个测试逻辑，这不仅减少了代码重复，更重要的是帮助我们系统地探索输入空间。

### 4.3.1 参数化测试的动机

传统测试的问题：
- 大量重复的测试代码
- 难以覆盖边界条件
- 新增测试用例麻烦
- 测试意图不清晰

参数化测试的优势：
- 数据与逻辑分离
- 易于添加新用例
- 清晰展示测试覆盖
- 更好的错误报告

### 4.3.2 参数化测试模式

1. **简单参数化**
   - 输入：多组参数值
   - 输出：对每组参数执行相同测试
   - 适用：等价类测试、边界值测试

2. **笛卡尔积参数化**
   - 输入：多个参数的可能值
   - 输出：所有组合的测试
   - 适用：组合测试、交互测试

3. **数据驱动测试**
   - 输入：外部数据源（CSV、JSON、数据库）
   - 输出：基于数据的测试
   - 适用：大规模测试、回归测试

### 4.3.3 参数化测试设计原则

1. **等价类划分**
   - 将输入域划分为等价类
   - 每个等价类选择代表值
   - 确保覆盖所有类别

2. **边界值分析**
   - 测试边界上的值
   - 测试边界附近的值
   - 考虑off-by-one错误

3. **组合策略**
   - 全组合：所有参数的所有组合
   - 配对测试：任意两个参数的所有组合
   - 正交数组：平衡覆盖与成本

### 4.3.4 参数化测试的实现

**基本形式**：
```
@parameterized([
    (输入1, 期望输出1),
    (输入2, 期望输出2),
    ...
])
def test_function(input, expected):
    assert function(input) == expected
```

**高级形式**：
- 参数命名：提高可读性
- 条件跳过：某些组合不适用
- 自定义标识：更好的错误报告

### 4.3.5 参数生成策略

1. **手动枚举**
   - 优点：精确控制
   - 缺点：可能遗漏
   - 适用：关键场景

2. **规则生成**
   - 范围生成：range(start, end)
   - 笛卡尔积：product(list1, list2)
   - 随机采样：sample(population, k)

3. **基于属性生成**
   - 使用假设（hypothesis）
   - 智能收缩失败用例
   - 自动边界探索

### 4.3.6 参数化测试的陷阱

1. **过度参数化**
   - 测试变得难以理解
   - 失去具体性
   - 调试困难

2. **不完整覆盖**
   - 遗漏重要组合
   - 忽视参数间依赖
   - 边界条件不足

3. **性能问题**
   - 组合爆炸
   - 测试时间过长
   - 资源消耗大

### 练习 4.3

1. 设计一个密码验证函数的参数化测试，要求密码8-20位，必须包含大小写字母和数字。

<details>
<summary>参考答案</summary>

密码验证参数化测试设计：

**测试参数设计**：
```
有效密码用例：
- "Abcd1234" - 最小长度，满足所有要求
- "AbcdEfgh12345678901" - 最大长度
- "aB3" + "x"*5 - 恰好8位
- "aB3" + "x"*17 - 恰好20位

无效密码用例：
- "Abcd123" - 太短（7位）
- "Abcd123" + "x"*14 - 太长（21位）
- "abcd1234" - 缺少大写
- "ABCD1234" - 缺少小写
- "AbcdEfgh" - 缺少数字
- "12345678" - 只有数字
- "" - 空密码
- "        " - 只有空格
```

**参数化策略**：
1. 长度边界测试：[7,8,9,19,20,21]
2. 字符组合测试：全排列(有大写,有小写,有数字,有特殊字符)
3. 特殊情况：空、null、Unicode字符

**测试组织**：
- 分组：有效密码组、无效密码组
- 每组使用清晰的测试描述
- 失败时报告具体的验证失败原因
</details>

2. 如何避免参数化测试中的组合爆炸？设计一个有4个参数，每个参数有5个可能值的测试策略。

<details>
<summary>参考答案</summary>

避免组合爆炸的策略：

**问题规模**：
- 全组合：5^4 = 625个测试
- 配对测试：约25-30个测试
- 正交数组：约25个测试

**解决方案**：

1. **配对测试（Pairwise Testing）**
   - 保证任意两个参数的所有组合都被覆盖
   - 使用工具如PICT生成测试用例
   - 覆盖率与成本的良好平衡

2. **基于风险的选择**
   - 识别高风险组合
   - 参数间的已知交互
   - 历史缺陷数据指导

3. **等价类代表**
   - 每个参数的5个值分组
   - 选择每组的代表值
   - 减少冗余测试

4. **渐进式测试**
   - 第一轮：每个参数的默认值组合
   - 第二轮：边界值组合
   - 第三轮：基于覆盖率的补充

**示例正交数组**（L25）：
```
测试用例数：25个（而非625个）
覆盖特性：
- 每个参数的每个值至少出现5次
- 任意两个参数的组合都被覆盖
- 检测大部分双因素交互缺陷
```

**实施建议**：
- 使用配对测试工具
- 记录未覆盖的组合
- 基于风险补充关键组合
- 监控生产环境的参数组合
</details>

### 进一步研究

- 自适应参数化：基于之前的测试结果动态调整参数？
- 参数化测试的可视化：如何直观展示参数空间的覆盖情况？
- 智能参数生成：使用机器学习预测高价值的参数组合？
- 参数依赖建模：如何表达和处理参数间的复杂依赖关系？
- 分布式参数化测试：如何有效并行执行大规模参数化测试？
- 参数化测试的维护：参数集演化时如何保持测试的有效性？

## 4.4 纯函数测试 vs. 有状态代码测试

测试的难易程度很大程度上取决于被测代码的性质。纯函数和有状态代码代表了两个极端，理解它们的测试差异对编写高质量测试至关重要。

### 4.4.1 纯函数的测试优势

纯函数具有两个关键特性：
1. **确定性**：相同输入总是产生相同输出
2. **无副作用**：不修改外部状态，不依赖外部状态

这些特性使纯函数成为测试的理想对象：

**简单直接的断言**
- 输入 → 输出的映射关系清晰
- 不需要复杂的setup和teardown
- 测试可以并行执行

**天然的隔离性**
- 不需要Mock外部依赖
- 不受测试执行顺序影响
- 易于理解和调试

**属性测试友好**
- 容易定义不变式和属性
- 可以使用数学性质验证
- 适合自动化测试生成

### 4.4.2 有状态代码的测试挑战

有状态代码包含或依赖可变状态，测试时需要考虑：

1. **状态管理**
   - 初始状态设置
   - 状态变化验证
   - 状态清理和重置

2. **顺序依赖**
   - 操作顺序影响结果
   - 测试间可能相互影响
   - 并发访问的复杂性

3. **隐藏依赖**
   - 全局变量
   - 单例模式
   - 环境变量

### 4.4.3 测试策略对比

**纯函数测试模式**：
```
给定输入 → 调用函数 → 验证输出
```

特点：
- 每个测试完全独立
- 可以使用表驱动测试
- 易于生成边界用例

**有状态代码测试模式**：
```
设置初始状态 → 执行操作序列 → 验证最终状态和副作用
```

特点：
- 需要仔细的状态管理
- 可能需要测试状态转换
- 验证不仅包括返回值

### 4.4.4 状态测试的设计模式

1. **Given-When-Then模式**
   - Given：设置初始状态
   - When：执行被测操作
   - Then：验证结果状态

2. **状态机测试**
   - 定义有效状态集合
   - 验证状态转换正确性
   - 检查非法状态转换

3. **快照测试**
   - 记录某时刻的完整状态
   - 比较操作前后的状态差异
   - 适合复杂对象的测试

### 4.4.5 重构向纯函数

为了提高可测试性，常见的重构技术：

1. **参数化依赖**
   ```
   # 有状态：依赖全局配置
   def process():
       if global_config.debug:
           log("processing")
       return compute()
   
   # 纯函数：参数化配置
   def process(config):
       if config.debug:
           return ("processing", compute())
       return (None, compute())
   ```

2. **分离副作用**
   ```
   # 混合逻辑和副作用
   def save_user(user):
       user.validate()
       user.hash_password()
       database.save(user)
   
   # 分离后
   def prepare_user(user):  # 纯函数
       validated = validate_user(user)
       return hash_password(validated)
   
   def save_user(user):  # 副作用集中
       prepared = prepare_user(user)
       database.save(prepared)
   ```

3. **命令查询分离（CQS）**
   - 查询：返回数据，不改变状态（纯函数）
   - 命令：改变状态，不返回数据
   - 避免既改变状态又返回数据

### 4.4.6 混合策略

实际系统中，纯函数和有状态代码往往混合存在：

1. **函数式核心，命令式外壳**
   - 核心逻辑用纯函数实现
   - 外层处理IO和状态管理
   - 大部分测试针对纯函数核心

2. **状态隔离**
   - 将状态封装在明确的边界内
   - 通过接口控制状态访问
   - 使用不可变数据结构

3. **事件溯源**
   - 状态变化表示为事件序列
   - 当前状态通过重放事件计算
   - 便于测试和调试

### 练习 4.4

1. 将以下有状态的购物车代码重构为更易测试的形式：
```
class ShoppingCart:
    items = []  # 类变量（共享状态）
    
    def add_item(self, item):
        self.items.append(item)
        if len(self.items) > 10:
            self.apply_bulk_discount()
    
    def apply_bulk_discount(self):
        for item in self.items:
            item.price *= 0.9
    
    def get_total(self):
        return sum(item.price for item in self.items)
```

<details>
<summary>参考答案</summary>

重构方案：

1. **消除共享状态**
```python
class ShoppingCart:
    def __init__(self):
        self._items = []  # 实例变量，非共享
```

2. **分离纯函数计算**
```python
# 纯函数：计算折扣
def calculate_discount(items_count, price):
    if items_count > 10:
        return price * 0.9
    return price

# 纯函数：计算总价
def calculate_total(items):
    return sum(item.price for item in items)

# 纯函数：应用折扣到商品列表
def apply_discount_to_items(items, discount_rate):
    return [
        Item(item.name, item.price * discount_rate)
        for item in items
    ]
```

3. **不可变的方法**
```python
class ImmutableShoppingCart:
    def __init__(self, items=None):
        self._items = tuple(items or [])
    
    def add_item(self, item):
        new_items = self._items + (item,)
        # 返回新购物车而非修改当前
        return ImmutableShoppingCart(new_items)
    
    def with_discounts(self):
        if len(self._items) > 10:
            discounted = apply_discount_to_items(
                self._items, 0.9
            )
            return ImmutableShoppingCart(discounted)
        return self
    
    @property
    def total(self):
        return calculate_total(self._items)
```

4. **测试友好的设计**
```python
# 易于测试的纯函数
def test_discount_calculation():
    assert calculate_discount(5, 100) == 100
    assert calculate_discount(11, 100) == 90

# 不可变对象的测试
def test_immutable_cart():
    cart1 = ImmutableShoppingCart()
    cart2 = cart1.add_item(Item("Book", 10))
    
    assert len(cart1._items) == 0  # cart1未改变
    assert len(cart2._items) == 1  # cart2是新对象
```

关键改进：
- 消除了共享状态
- 分离了纯计算逻辑
- 提供了不可变选项
- 每个函数职责单一
- 测试变得简单直接
</details>

2. 设计一个测试策略，用于测试具有复杂状态转换的有限状态机。

<details>
<summary>参考答案</summary>

有限状态机测试策略：

1. **状态覆盖测试**
   - 确保每个状态都被访问
   - 验证每个状态的属性
   - 测试初始和终止状态

2. **转换覆盖测试**
   - 每个有效转换至少执行一次
   - 验证转换条件
   - 测试转换的副作用

3. **路径测试**
   - 关键业务流程的完整路径
   - 最短路径和最长路径
   - 循环路径（如果存在）

4. **负面测试**
   - 非法状态转换尝试
   - 无效输入处理
   - 边界条件

5. **属性测试**
   ```
   属性1：从任意状态出发，不应到达非法状态
   属性2：确定性 - 相同状态+输入→相同结果
   属性3：可达性 - 从初始状态可达所有有效状态
   ```

6. **测试实现示例**
   ```python
   class FSMTester:
       def __init__(self, fsm):
           self.fsm = fsm
           self.visited_states = set()
           self.executed_transitions = set()
       
       def verify_state_properties(self, state):
           # 验证状态不变式
           assert state in self.fsm.valid_states
           assert self.fsm.check_invariants(state)
       
       def test_all_transitions(self):
           # 使用BFS遍历所有可达状态
           queue = [self.fsm.initial_state]
           visited = set()
           
           while queue:
               state = queue.pop(0)
               if state in visited:
                   continue
               
               visited.add(state)
               self.verify_state_properties(state)
               
               # 测试所有出边
               for event in self.fsm.get_events(state):
                   next_state = self.fsm.transition(
                       state, event
                   )
                   self.executed_transitions.add(
                       (state, event, next_state)
                   )
                   queue.append(next_state)
   ```

7. **模型检测集成**
   - 使用TLA+或Alloy描述状态机
   - 验证安全性和活性属性
   - 自动生成测试用例

8. **可视化辅助**
   - 生成状态图
   - 高亮已测试/未测试的转换
   - 识别不可达状态
</details>

### 进一步研究

- 纯度分析：如何自动检测函数的纯度？
- 效果系统：类型系统如何帮助区分纯函数和副作用？
- 测试单子：函数式编程中的IO测试策略？
- 状态最小化：如何识别和消除不必要的状态？
- 并发状态测试：如何测试并发访问下的状态一致性？
- 状态恢复测试：系统崩溃后的状态恢复如何验证？

## 4.5 流行框架概览

单元测试框架是测试实践的基石。理解不同框架的设计理念和特性，有助于选择合适的工具并充分发挥其潜力。

### 4.5.1 xUnit家族

xUnit架构模式源自Smalltalk的SUnit，由Kent Beck创建，影响了几乎所有现代测试框架。

**核心概念**：
- **Test Case**：单个测试的容器
- **Test Suite**：测试集合
- **Test Fixture**：测试环境的setup/teardown
- **Assertions**：验证期望结果

**设计原则**：
1. 每个测试独立运行
2. 测试顺序不应影响结果
3. 失败应该提供清晰信息
4. 测试代码应该简单

### 4.5.2 JUnit（Java）

JUnit是Java生态系统的标准测试框架，其设计影响了许多其他语言的测试框架。

**JUnit 5架构**：
```
JUnit 5 = JUnit Platform + JUnit Jupiter + JUnit Vintage
         测试运行平台      新编程模型       兼容旧版本
```

**关键特性**：
- 注解驱动：@Test, @BeforeEach, @AfterEach
- 参数化测试：@ParameterizedTest
- 嵌套测试：@Nested实现测试分组
- 动态测试：运行时生成测试
- 扩展模型：自定义测试生命周期

**独特优势**：
- 强大的IDE集成
- 丰富的断言库（AssertJ, Hamcrest）
- 并行执行支持
- 详细的测试报告

### 4.5.3 pytest（Python）

pytest采用了与xUnit不同的理念，强调简洁和Pythonic。

**设计哲学**：
- 使用普通assert语句
- 自动测试发现
- 强大的fixture系统
- 插件架构

**核心特性**：

1. **Fixture系统**
   - 依赖注入风格
   - 作用域控制（function/class/module/session）
   - 参数化fixture
   - fixture工厂

2. **标记系统**
   - @pytest.mark.skip：条件跳过
   - @pytest.mark.parametrize：参数化
   - 自定义标记：组织和筛选测试

3. **断言重写**
   - 智能的失败信息
   - 显示表达式中间值
   - 自定义断言解释

**生态系统**：
- pytest-cov：覆盖率集成
- pytest-mock：Mock支持
- pytest-xdist：分布式执行
- pytest-timeout：超时控制

### 4.5.4 Jest（JavaScript）

Jest由Facebook开发，专注于简单性和开发体验。

**核心理念**：
- 零配置
- 快照测试
- 并行隔离
- 强大的Mock能力

**特色功能**：

1. **快照测试**
   - 自动记录输出
   - 检测意外变化
   - 适合UI组件测试

2. **Mock系统**
   - 自动Mock模块
   - 计时器Mock
   - 手动Mock目录

3. **监视模式**
   - 只运行相关测试
   - 基于Git状态
   - 交互式测试选择

**性能优化**：
- 智能测试运行顺序
- 并行进程池
- 增量文件系统缓存

### 4.5.5 框架选择考虑因素

1. **语言生态系统**
   - 社区标准
   - 工具链集成
   - 可用资源

2. **项目需求**
   - 测试复杂度
   - 性能要求
   - 团队熟悉度

3. **特殊功能需求**
   - 并行执行
   - 参数化测试
   - Mock能力
   - 报告生成

4. **集成需求**
   - CI/CD支持
   - IDE集成
   - 代码覆盖率
   - 调试能力

### 4.5.6 框架对比

| 特性 | JUnit 5 | pytest | Jest |
|------|---------|--------|------|
| 断言风格 | 专用方法 | 原生assert | expect链式 |
| 参数化 | 注解 | 装饰器 | each语法 |
| Mock支持 | 需要Mockito | pytest-mock | 内置 |
| 并行执行 | 内置 | 插件 | 默认 |
| 配置复杂度 | 中等 | 低 | 零配置 |
| 扩展性 | 高 | 极高 | 中等 |

### 4.5.7 新兴趋势

1. **属性基础测试集成**
   - JUnit-QuickCheck
   - Hypothesis for pytest
   - fast-check for Jest

2. **可视化测试**
   - 测试结果可视化
   - 覆盖率热图
   - 失败分析工具

3. **AI辅助功能**
   - 测试生成
   - 失败诊断
   - 测试优化建议

### 练习 4.5

1. 比较三个框架中参数化测试的语法，分析各自的优缺点。

<details>
<summary>参考答案</summary>

**JUnit 5参数化测试**：
```java
@ParameterizedTest
@ValueSource(ints = {1, 3, 5, -3, 15})
void testIsOdd(int number) {
    assertTrue(isOdd(number));
}

@ParameterizedTest
@CsvSource({
    "apple, 5",
    "banana, 6", 
    "cherry, 6"
})
void testLength(String fruit, int length) {
    assertEquals(length, fruit.length());
}
```

优点：
- 类型安全
- 多种数据源（CSV、方法、枚举等）
- IDE支持好

缺点：
- 语法较冗长
- 需要额外注解

**pytest参数化测试**：
```python
@pytest.mark.parametrize("number", [1, 3, 5, -3, 15])
def test_is_odd(number):
    assert is_odd(number)

@pytest.mark.parametrize("fruit,length", [
    ("apple", 5),
    ("banana", 6),
    ("cherry", 6)
])
def test_length(fruit, length):
    assert len(fruit) == length
```

优点：
- 语法简洁
- 灵活的参数命名
- 可组合多个parametrize

缺点：
- 字符串参数名容易出错
- 大数据集时可读性降低

**Jest参数化测试**：
```javascript
test.each([1, 3, 5, -3, 15])(
  'isOdd(%i) returns true',
  (number) => {
    expect(isOdd(number)).toBe(true);
  }
);

test.each`
  fruit      | length
  ${'apple'} | ${5}
  ${'banana'}| ${6}
  ${'cherry'}| ${6}
`('$fruit has length $length', ({fruit, length}) => {
  expect(fruit.length).toBe(length);
});
```

优点：
- 模板字符串表格语法直观
- 测试名称模板化
- 支持多种格式

缺点：
- 模板字符串语法学习曲线
- 类型推断可能不准确

**总结**：
- JUnit 5：适合大型项目，重视类型安全
- pytest：Python风格，简洁灵活
- Jest：现代JavaScript风格，注重开发体验
</details>

2. 设计一个测试框架评估矩阵，用于为新项目选择合适的框架。

<details>
<summary>参考答案</summary>

**测试框架评估矩阵**：

1. **功能完整性（权重：25%）**
   - 基本断言能力
   - 参数化测试
   - 异步测试支持
   - Mock/Stub能力
   - 测试组织（套件、标签）

2. **易用性（权重：20%）**
   - 学习曲线
   - 文档质量
   - 错误信息清晰度
   - 调试支持
   - 配置简单性

3. **性能（权重：15%）**
   - 启动时间
   - 并行执行
   - 大型测试套件性能
   - 内存使用
   - 增量测试能力

4. **生态系统（权重：20%）**
   - 社区活跃度
   - 插件可用性
   - IDE支持
   - CI/CD集成
   - 相关工具

5. **可维护性（权重：10%）**
   - 测试代码可读性
   - 重构友好度
   - 版本稳定性
   - 向后兼容性
   - 迁移成本

6. **特殊需求（权重：10%）**
   - 快照测试
   - 可视化测试
   - 属性测试
   - 覆盖率集成
   - 报告生成

**评分标准**：
- 5分：优秀，完全满足需求
- 4分：良好，基本满足需求
- 3分：一般，需要额外工作
- 2分：较差，有明显缺陷
- 1分：不可接受

**决策流程**：
1. 根据项目特点调整权重
2. 评估候选框架
3. 计算加权得分
4. 考虑团队经验
5. 进行概念验证
6. 做出最终决定

**示例评估结果**：
| 框架 | 功能 | 易用 | 性能 | 生态 | 维护 | 特殊 | 总分 |
|------|------|------|------|------|------|------|------|
| Framework A | 4.5 | 4.0 | 3.5 | 4.5 | 4.0 | 3.0 | 4.05 |
| Framework B | 4.0 | 4.5 | 4.0 | 3.5 | 4.5 | 4.0 | 4.08 |
| Framework C | 3.5 | 3.0 | 4.5 | 3.0 | 3.5 | 4.5 | 3.58 |
</details>

### 进一步研究

- 测试框架的性能基准：如何公平比较不同框架的性能？
- 多语言项目的框架选择：如何在多语言项目中保持测试一致性？
- 测试框架的可扩展性设计：什么使得框架易于扩展？
- 下一代测试框架：未来测试框架会有哪些创新？
- 框架迁移策略：如何从一个框架迁移到另一个？
- 领域特定测试框架：为特定领域设计测试框架的考虑？

## 本章小结

本章深入探讨了单元测试的理论与实践。我们从TDD的哲学开始，理解了测试如何驱动设计。通过测试替身的学习，掌握了隔离被测单元的技术。参数化测试展示了如何系统地探索输入空间。纯函数与有状态代码的对比，揭示了可测试性的本质。最后，流行框架的概览为工具选择提供了指导。

关键要点：
1. TDD不仅是测试技术，更是设计方法
2. 合理使用测试替身，避免过度Mock
3. 参数化测试提高测试覆盖的效率
4. 设计时考虑可测试性，倾向纯函数
5. 选择框架要考虑项目需求和团队情况

下一章，我们将探讨集成测试，了解如何测试组件间的交互。