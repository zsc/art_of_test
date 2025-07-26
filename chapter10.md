# 第10章：基于性质的测试

基于性质的测试（Property-Based Testing, PBT）是一种强大的测试方法，它从测试具体示例转向测试通用性质。通过自动生成测试数据并验证程序在所有输入上都满足指定性质，PBT能够发现传统测试方法难以触及的边界情况。本章将深入探讨PBT的理论基础、实践技术和高级应用。

## 10.1 从示例到性质

传统测试依赖具体示例，而基于性质的测试关注普遍规律。这种范式转变需要不同的思维方式。

### 10.1.1 示例测试的局限

**具体性困境**：
- 有限的测试用例无法覆盖无限的输入空间
- 人类倾向于选择"正常"输入
- 边界情况容易被遗漏
- 维护大量示例测试的成本

**认知偏见**：
- 确认偏见：倾向于编写会通过的测试
- 可用性启发：基于容易想到的例子
- 代表性启发：假设典型例子代表全部

### 10.1.2 性质的本质

**什么是性质**：
- 对所有有效输入都成立的断言
- 输入与输出之间的关系
- 函数的不变式
- 代数定律的表达

**性质的分类**：
1. **不变式**：操作前后保持不变的条件
2. **幂等性**：f(f(x)) = f(x)
3. **交换律**：f(a,b) = f(b,a)
4. **结合律**：f(f(a,b),c) = f(a,f(b,c))
5. **分配律**：f(a,g(b,c)) = g(f(a,b),f(a,c))
6. **逆运算**：f(g(x)) = x

### 10.1.3 发现性质的方法

**从规范出发**：
- 形式化需求文档
- 数学定义
- 业务规则

**从实现推导**：
- 观察代码模式
- 识别不变条件
- 分析数据流

**从测试泛化**：
- 找出示例的共同模式
- 抽象具体值为变量
- 识别关系而非数值

### 10.1.4 性质设计原则

**完备性**：
- 性质集合应该唯一确定正确实现
- 避免欠约束（允许错误实现）
- 避免过约束（排除正确实现）

**可测试性**：
- 性质应该可高效验证
- 避免存在量词（难以测试）
- 优先使用可判定的性质

**可理解性**：
- 性质应该清晰表达意图
- 分解复杂性质为简单组合
- 使用领域术语

### 练习 10.1

1. 将以下排序函数的示例测试转换为性质。

示例测试：
```
test_sort([3,1,2]) = [1,2,3]
test_sort([1]) = [1]
test_sort([]) = []
```

<details>
<summary>参考答案</summary>

排序函数的性质：

1. **有序性**：
   ```
   ∀ list. ∀ i < len(sort(list))-1. 
   sort(list)[i] ≤ sort(list)[i+1]
   ```

2. **置换性**（保持元素）：
   ```
   ∀ list. multiset(sort(list)) = multiset(list)
   ```

3. **幂等性**：
   ```
   ∀ list. sort(sort(list)) = sort(list)
   ```

4. **最小元素性质**：
   ```
   ∀ list. list ≠ [] → 
   sort(list)[0] = min(list)
   ```

5. **长度保持**：
   ```
   ∀ list. len(sort(list)) = len(list)
   ```

6. **稳定性**（如果适用）：
   ```
   ∀ list. ∀ i,j. i < j ∧ list[i] = list[j] →
   index(sort(list), list[i]) < index(sort(list), list[j])
   ```
</details>

2. 识别一个常见函数（如字符串反转）的完整性质集。

<details>
<summary>参考答案</summary>

字符串反转的完整性质集：

1. **对合性**（自逆）：
   ```
   ∀ s: string. reverse(reverse(s)) = s
   ```

2. **长度保持**：
   ```
   ∀ s: string. len(reverse(s)) = len(s)
   ```

3. **字符映射**：
   ```
   ∀ s: string. ∀ i < len(s). 
   reverse(s)[i] = s[len(s)-1-i]
   ```

4. **空串不变**：
   ```
   reverse("") = ""
   ```

5. **单字符不变**：
   ```
   ∀ c: char. reverse(str(c)) = str(c)
   ```

6. **连接分配**（反向）：
   ```
   ∀ s1,s2: string. 
   reverse(s1 + s2) = reverse(s2) + reverse(s1)
   ```

7. **回文检测**：
   ```
   ∀ s: string. isPalindrome(s) ↔ reverse(s) = s
   ```

这个性质集完整定义了反转操作，任何满足这些性质的函数必然是正确的字符串反转实现。
</details>

### 进一步研究

- 性质完备性的形式化定义
- 从机器学习模型中提取性质
- 性质的最小化和简化算法
- 性质之间的依赖关系分析

## 10.2 生成器和缩小

生成器是PBT的核心组件，负责产生测试输入；缩小则帮助找到最小失败用例。

### 10.2.1 生成器设计

**基本生成器**：
- 原子类型：整数、浮点数、布尔值
- 容器类型：列表、集合、映射
- 复合类型：元组、记录、树

**生成策略**：
- 均匀分布
- 偏向边界值
- 指数分布（偏向小值）
- 正态分布

**组合子**：
- map：转换生成的值
- filter：筛选满足条件的值
- flatMap：依赖生成
- frequency：加权选择

### 10.2.2 自定义生成器

**代数数据类型**：
```haskell
-- 二叉树生成器
genTree :: Gen a -> Gen (Tree a)
genTree genA = sized $ \n ->
  if n == 0
  then Leaf <$> genA
  else frequency
    [(1, Leaf <$> genA),
     (n, Node <$> genA <*> subtree <*> subtree)]
  where subtree = resize (n `div` 2) (genTree genA)
```

**约束满足**：
- 前置条件过滤
- 智能生成（直接满足约束）
- 回溯生成

**相关数据**：
- 依赖关系
- 不变式维护
- 有效状态生成

### 10.2.3 缩小算法

**缩小的目标**：
- 找到最小的失败输入
- 保持失败性质
- 快速收敛

**缩小策略**：
1. **结构缩小**：
   - 列表：删除元素、子列表
   - 树：子树替换
   - 数字：二分逼近

2. **类型特定缩小**：
   - 字符串：删除字符、子串
   - 集合：删除元素、子集
   - 函数：简化定义域

3. **通用框架**：
   ```
   shrink :: a -> [a]  -- 产生更小的候选值
   
   minimize :: (a -> Bool) -> a -> a
   minimize fails x
     | null candidates = x
     | otherwise = minimize fails (head failing)
     where
       candidates = shrink x
       failing = filter fails candidates
   ```

### 10.2.4 生成质量

**覆盖率指标**：
- 值域覆盖
- 结构复杂度分布
- 边界值频率

**偏差检测**：
- 统计测试
- 可视化分布
- 熵度量

**优化技术**：
- 自适应生成
- 覆盖引导
- 学习失败模式

### 练习 10.2

1. 设计一个生成有效电子邮件地址的生成器。

<details>
<summary>参考答案</summary>

电子邮件生成器设计：

```haskell
-- 基础组件
genLocalPart :: Gen String
genLocalPart = do
  -- 长度1-64
  len <- choose (1, 64)
  -- 首尾不能是点
  middle <- vectorOf (len-2) localChar
  first <- localCharNoDot
  last <- localCharNoDot
  return $ first : middle ++ [last]
  where
    localChar = frequency
      [(26, choose ('a', 'z')),
       (26, choose ('A', 'Z')),
       (10, choose ('0', '9')),
       (1, elements ".-_")]
    localCharNoDot = 
      oneof [choose ('a', 'z'),
             choose ('A', 'Z'),
             choose ('0', '9')]

genDomain :: Gen String
genDomain = do
  -- 子域名
  subdomains <- listOf1 genLabel
  -- 顶级域名
  tld <- elements ["com", "org", "net", "edu"]
  return $ intercalate "." (subdomains ++ [tld])
  where
    genLabel = do
      len <- choose (1, 63)
      label <- vectorOf len $ 
        oneof [choose ('a', 'z'),
               choose ('0', '9')]
      return label

genEmail :: Gen String
genEmail = do
  local <- genLocalPart
  domain <- genDomain
  return $ local ++ "@" ++ domain

-- 缩小策略
shrinkEmail :: String -> [String]
shrinkEmail email = 
  let (local, domain) = break (== '@') email
  in [l ++ "@" ++ domain | l <- shrinkString local] ++
     [local ++ "@" ++ d | d <- shrinkDomain (tail domain)]
```

关键考虑：
- RFC 5322规范遵守
- 常见模式优先
- 边界情况包含
- 有效缩小路径
</details>

2. 实现一个通用的列表缩小算法，保持某个性质。

<details>
<summary>参考答案</summary>

保持性质的列表缩小：

```haskell
-- 通用列表缩小，保持性质P
shrinkListWith :: (a -> [a]) -> ([a] -> Bool) -> [a] -> [[a]]
shrinkListWith shrinkElem property xs = 
  filter property allShrinks
  where
    allShrinks = 
      -- 删除元素
      removes xs ++
      -- 取子列表
      sublists xs ++
      -- 缩小单个元素
      shrinkOne xs
      
    -- 删除单个元素
    removes [] = []
    removes (x:xs) = xs : map (x:) (removes xs)
    
    -- 连续子列表
    sublists xs = 
      [take n xs | n <- [0..length xs - 1]] ++
      [drop n xs | n <- [1..length xs]]
    
    -- 缩小单个元素
    shrinkOne [] = []
    shrinkOne (x:xs) = 
      [x':xs | x' <- shrinkElem x] ++
      [x:xs' | xs' <- shrinkOne xs]

-- 特殊化：保持有序性
shrinkSorted :: Ord a => (a -> [a]) -> [a] -> [[a]]
shrinkSorted = shrinkListWith isSorted
  where isSorted xs = sort xs == xs

-- 特殊化：保持唯一性  
shrinkUnique :: Eq a => (a -> [a]) -> [a] -> [[a]]
shrinkUnique = shrinkListWith hasNoDups
  where hasNoDups xs = nub xs == xs

-- 使用示例
-- 缩小一个保持递增的列表
shrinkIncreasing :: [Int] -> [[Int]]
shrinkIncreasing = shrinkListWith shrinkInt isIncreasing
  where 
    isIncreasing [] = True
    isIncreasing [_] = True
    isIncreasing (x:y:rest) = x < y && isIncreasing (y:rest)
```

这个设计：
- 模块化：缩小逻辑与性质检查分离
- 高效：避免生成无效候选
- 通用：适用于任何列表性质
- 可组合：可以组合多个性质
</details>

### 进一步研究

- 基于覆盖的自适应生成策略
- 使用机器学习指导缩小过程
- 生成器的形式化规范和验证
- 概率生成器的理论基础

## 10.3 有状态性质测试

测试有状态系统需要考虑操作序列和状态演化，这带来了额外的复杂性。

### 10.3.1 状态机模型

**抽象状态机**：
- 状态空间定义
- 初始状态
- 状态转换
- 前置条件
- 后置条件

**模型与实现**：
- 模型状态 vs 系统状态
- 抽象函数
- 一致性关系

### 10.3.2 命令生成

**命令序列**：
- 有效命令生成
- 前置条件检查
- 依赖关系处理

**状态相关生成**：
```haskell
-- 银行账户示例
data Command = 
    OpenAccount String
  | Deposit String Amount
  | Withdraw String Amount
  | Transfer String String Amount

genCommand :: ModelState -> Gen Command
genCommand state = 
  frequency $ 
    [(1, OpenAccount <$> genNewId)] ++
    (if hasAccounts state then
      [(3, Deposit <$> genExistingId <*> genAmount),
       (3, Withdraw <$> genExistingId <*> genAmount),
       (2, Transfer <$> genExistingId <*> genExistingId <*> genAmount)]
     else [])
```

### 10.3.3 线性化测试

**并发正确性**：
- 操作的原子性
- 线性化点
- 历史验证

**算法**：
1. 并发执行操作
2. 记录调用和返回时间
3. 寻找合法的串行化
4. 验证结果一致性

### 10.3.4 状态不变式

**全局不变式**：
- 始终成立的条件
- 跨操作的约束
- 资源守恒

**时序性质**：
- 最终一致性
- 进度保证
- 公平性

**故障注入**：
- 操作失败模拟
- 部分状态恢复
- 异常路径测试

### 练习 10.3

1. 设计一个分布式计数器的状态机模型和性质。

<details>
<summary>参考答案</summary>

分布式计数器模型：

```haskell
-- 模型定义
data NodeId = NodeA | NodeB | NodeC
  deriving (Eq, Ord, Show)

data ModelState = ModelState
  { nodeValues :: Map NodeId Int
  , totalValue :: Int
  , network :: NetworkState
  }

data Command = 
    Increment NodeId Int
  | Decrement NodeId Int  
  | Sync NodeId NodeId  -- 从第一个同步到第二个
  | PartitionNodes [NodeId] [NodeId]
  | HealPartition

-- 状态转换
transition :: ModelState -> Command -> ModelState
transition s (Increment node n) = 
  s { nodeValues = Map.adjust (+n) node (nodeValues s)
    , totalValue = totalValue s + n }
    
transition s (Sync from to) = 
  if canCommunicate (network s) from to then
    let fromVal = nodeValues s Map.! from
        toVal = nodeValues s Map.! to
        merged = max fromVal toVal  -- CRDT合并
    in s { nodeValues = Map.insert to merged $
                       Map.insert from merged $ 
                       nodeValues s }
  else s  -- 网络分区，同步失败

-- 性质定义
properties :: [Property]
properties = 
  [ -- 1. 最终一致性
    prop_eventualConsistency = 
      forAll (genCommandSequence `endingWith` fullSync) $ \cmds ->
        let final = execute cmds
            values = Map.elems (nodeValues final)
        in all (== head values) (tail values)
        
  , -- 2. 单调性（只增计数器）
    prop_monotonicity = 
      forAll genCommandSequence $ \cmds ->
        let states = scanl transition initial cmds
            nodeHistories = 
              [ map (\s -> nodeValues s Map.! n) states 
              | n <- [NodeA, NodeB, NodeC]]
        in all isMonotonic nodeHistories
        
  , -- 3. 值守恒（无分区时）
    prop_conservation = 
      forAll (genCommandSequence `without` partitions) $ \cmds ->
        let final = execute cmds
        in sum (Map.elems (nodeValues final)) == 
           totalValue final
           
  , -- 4. 收敛性
    prop_convergence = 
      forAll genConvergentSequence $ \cmds ->
        measureConvergence (execute cmds) < epsilon
  ]

-- 辅助函数
isMonotonic :: [Int] -> Bool
isMonotonic xs = and $ zipWith (<=) xs (tail xs)

fullSync :: [Command]
fullSync = [Sync a b | a <- nodes, b <- nodes, a /= b]

measureConvergence :: ModelState -> Double
measureConvergence s = 
  let vals = Map.elems (nodeValues s)
      avg = fromIntegral (sum vals) / fromIntegral (length vals)
  in sum [abs (fromIntegral v - avg) | v <- vals]
```

关键性质：
- 最终一致性（网络恢复后）
- 单调递增（CRDT特性）
- 操作交换性
- 并发安全性
</details>

2. 实现一个简化的线性化检查算法。

<details>
<summary>参考答案</summary>

简化的线性化检查：

```haskell
-- 操作记录
data Event a = Call ThreadId a Time
             | Return ThreadId a Time
             deriving (Eq, Show)

-- 检查历史是否可线性化
isLinearizable :: Eq a => 
  (state -> a -> (state, result)) ->  -- 串行语义
  state ->                             -- 初始状态
  [Event a] ->                         -- 并发历史
  Bool
isLinearizable step initial history =
  any (checkSequence step initial) (allLinearizations history)

-- 生成所有可能的线性化
allLinearizations :: [Event a] -> [[a]]
allLinearizations events = 
  let ops = groupByThread events
      -- 找出所有保持程序顺序的排列
  in filter (respectsProgramOrder ops) 
            (permutations (concurrentOps events))

-- 检查一个串行序列是否产生观察到的结果
checkSequence :: Eq a =>
  (state -> a -> (state, result)) ->
  state -> 
  [a] -> 
  Bool
checkSequence step initial ops =
  let results = evalState (mapM stepM ops) initial
      stepM op = do
        s <- get
        let (s', r) = step s op
        put s'
        return (op, r)
  in results == observedResults
  
-- 优化：使用回溯搜索而非生成所有排列
linearizableBacktrack :: Eq a =>
  (state -> a -> (state, result)) ->
  state ->
  [Event a] ->
  Bool
linearizableBacktrack step initial history =
  search initial [] pending
  where
    pending = extractOps history
    
    search state done [] = 
      checkResults state done
      
    search state done pending =
      any tryOp (readyOps pending)
      where
        tryOp op = 
          let (state', result) = step state op
              done' = done ++ [(op, result)]
              pending' = remove op pending
          in search state' done' pending'
          
    readyOps ops = 
      filter (canExecute ops) ops
      
    canExecute ops op =
      all (happensBefore op) (dependencies op)
```

这个实现：
- 处理并发操作的交错
- 保持线程内的程序顺序
- 验证结果一致性
- 使用回溯优化搜索
</details>

### 进一步研究

- 分布式系统的状态模型抽象
- 弱一致性模型的性质表达
- 状态空间缩减技术
- 并发测试的确定性重放

## 10.4 QuickCheck及其衍生品

QuickCheck开创了基于性质测试的实践，其设计理念影响了众多语言的测试框架。

### 10.4.1 QuickCheck核心设计

**Haskell原版特点**：
- 类型类驱动的生成器
- 纯函数式设计
- 可组合的性质
- 灵活的配置

**核心抽象**：
```haskell
class Arbitrary a where
  arbitrary :: Gen a
  shrink :: a -> [a]

newtype Gen a = Gen (StdGen -> Int -> a)

quickCheck :: Testable prop => prop -> IO ()
```

### 10.4.2 语言适配

**Erlang PropEr**：
- 适应Erlang/OTP
- 状态机测试强化
- 并发特性支持

**Scala ScalaCheck**：
- 与类型系统集成
- 支持高阶类型
- 效果追踪

**Python Hypothesis**：
- 装饰器API
- 数据库支持
- 统计信息

**Rust proptest**：
- 宏驱动
- 借用检查器友好
- 策略组合子

### 10.4.3 高级特性

**标签和分类**：
- 测试案例分类
- 覆盖率统计
- 分布验证

**条件性质**：
- 前置条件处理
- 条件概率
- 拒绝率控制

**有状态测试**：
- 模型定义DSL
- 并发执行
- 时序验证

### 10.4.4 最佳实践

**性质设计模式**：
1. **往返性质**：encode(decode(x)) = x
2. **模型对照**：optimized(x) = simple(x)
3. **不变式维护**：op(x) satisfies inv
4. **代数定律**：群、环、格等结构

**测试组织**：
- 性质分组
- 依赖管理
- 渐进复杂度

**调试技巧**：
- 详细日志
- 中间状态检查
- 反例重放

### 练习 10.4

1. 使用QuickCheck风格测试一个LRU缓存实现。

<details>
<summary>参考答案</summary>

LRU缓存的性质测试：

```haskell
-- LRU缓存接口
data Cache k v = Cache
class LRUCache cache where
  empty :: Int -> cache k v
  get :: Ord k => k -> cache k v -> (Maybe v, cache k v)
  put :: Ord k => k -> v -> cache k v -> cache k v
  size :: cache k v -> Int
  capacity :: cache k v -> Int

-- 性质定义
prop_capacity :: (LRUCache c, Ord k, Arbitrary k, Arbitrary v) => 
  Positive Int -> [(k, v)] -> Bool
prop_capacity (Positive cap) ops =
  let cache = foldl' (\c (k,v) -> put k v c) (empty cap) ops
  in size cache <= capacity cache

prop_get_after_put :: (LRUCache c, Ord k, Eq v) =>
  k -> v -> c k v -> Bool
prop_get_after_put k v cache =
  let cache' = put k v cache
      (result, _) = get k cache'
  in result == Just v

prop_lru_eviction :: (LRUCache c, Ord k, Eq v, Show k, Show v) =>
  Positive Int -> Property
prop_lru_eviction (Positive cap) =
  forAll (genDistinctPairs (cap + 1)) $ \pairs ->
  let cache = foldl' (\c (k,v) -> put k v c) (empty cap) pairs
      (oldest:rest) = pairs
      (oldestKey, _) = oldest
      (result, _) = get oldestKey cache
  in classify (length pairs > cap) "eviction triggered" $
     result == Nothing

-- 模型对照测试
prop_model_equivalence :: (LRUCache c, Ord k, Eq v) =>
  Positive Int -> [CacheOp k v] -> Bool
prop_model_equivalence (Positive cap) ops =
  let (results1, _) = runOps (empty cap) ops
      (results2, _) = runOps (emptyModel cap) ops
  in results1 == results2

-- 操作生成器
data CacheOp k v = Get k | Put k v
  deriving (Show, Eq)

genCacheOps :: (Arbitrary k, Arbitrary v) => Gen [CacheOp k v]
genCacheOps = sized $ \n -> do
  keys <- vectorOf (n `div` 2) arbitrary
  let genOp = frequency
        [(1, Get <$> elements keys),
         (3, Put <$> arbitrary <*> arbitrary)]
  vectorOf n genOp

-- 状态机性质
prop_state_machine :: (LRUCache c, Ord k, Eq v) =>
  Positive Int -> Property
prop_state_machine (Positive cap) =
  forAllCommands (cacheModel cap) $ \cmds ->
  monadicIO $ do
    cache <- run $ newIORef (empty cap)
    results <- run $ mapM (execCmd cache) cmds
    assert $ verifyResults results

-- 并发性质
prop_concurrent_safe :: (LRUCache c, Ord k, Eq v) =>
  Positive Int -> Property  
prop_concurrent_safe (Positive cap) =
  forAll (genConcurrentOps 3 10) $ \ops ->
  monadicIO $ do
    cache <- run $ newMVar (empty cap)
    results <- run $ executeConcurrently cache ops
    assert $ isLinearizable results
```

关键测试点：
- 容量限制遵守
- LRU驱逐策略
- 并发安全性
- 与简单模型等价
</details>

2. 比较不同语言中QuickCheck实现的设计权衡。

<details>
<summary>参考答案</summary>

QuickCheck实现对比：

**Haskell (原版QuickCheck)**
优势：
- 类型系统完美契合
- 惰性求值支持无限结构
- 纯函数易于测试
- 强大的类型类机制

权衡：
- 需要理解Monad等概念
- IO测试相对复杂

**Python (Hypothesis)**
优势：
- 装饰器语法直观
- 自动持久化失败用例
- 集成pytest生态
- 优秀的错误信息

权衡：
- 运行时类型检查开销
- 生成器定义较冗长
- 缩小算法受动态类型限制

**Rust (proptest)**
优势：
- 零成本抽象
- 内存安全保证
- 宏简化使用
- 并发测试安全

权衡：
- 编译时间增加
- 生命周期复杂性
- 学习曲线陡峭

**JavaScript/TypeScript (fast-check)**
优势：
- 异步测试支持好
- 浏览器环境可用
- TypeScript类型推导
- 生态系统丰富

权衡：
- 性能相对较差
- 类型系统限制
- 异步复杂性

**设计决策对比**：

1. **API风格**：
   - Haskell: 组合子
   - Python: 装饰器
   - Rust: 宏
   - JS: 链式调用

2. **生成器定义**：
   - Haskell: 类型类
   - Python: 策略对象
   - Rust: 策略trait
   - JS: 生成器函数

3. **缩小策略**：
   - Haskell: 集成类型类
   - Python: 自动推导
   - Rust: 显式定义
   - JS: 可选配置

4. **并发支持**：
   - Haskell: STM天然支持
   - Python: 多线程限制
   - Rust: 无畏并发
   - JS: Promise/async

选择建议：
- 函数式纯度高→Haskell
- 快速原型→Python
- 系统编程→Rust
- Web开发→JavaScript
</details>

### 进一步研究

- QuickCheck的范畴论基础
- 效果系统中的性质测试
- 分布式QuickCheck实现
- 性质测试的形式化语义

## 10.5 与类型系统的集成

将性质测试与类型系统结合可以获得更强的正确性保证，这是未来测试技术的重要方向。

### 10.5.1 依赖类型中的性质

**类型即性质**：
- 精化类型
- 依赖对（Σ类型）
- 证明携带代码

**Liquid Haskell示例**：
```haskell
{-@ type Pos = {v:Int | v > 0} @-}
{-@ divide :: Int -> Pos -> Int @-}
divide :: Int -> Int -> Int
divide x y = x `div` y  -- 类型保证y非零

{-@ type SortedList a = [a]<{\x y -> x <= y}> @-}
{-@ sort :: Ord a => [a] -> SortedList a @-}
```

### 10.5.2 类型驱动生成

**GADTs和生成器**：
```haskell
data Expr a where
  Lit :: a -> Expr a
  Add :: Num a => Expr a -> Expr a -> Expr a
  Eq :: Eq a => Expr a -> Expr a -> Expr Bool
  If :: Expr Bool -> Expr a -> Expr a -> Expr a

genExpr :: (Arbitrary a, Typeable a) => Int -> Gen (Expr a)
genExpr 0 = Lit <$> arbitrary
genExpr n = oneof $ [Lit <$> arbitrary] ++
  [Add <$> subexpr <*> subexpr | isNum @a] ++
  [If <$> genExpr @Bool (n-1) <*> subexpr <*> subexpr]
  where subexpr = genExpr (n `div` 2)
```

### 10.5.3 类型级别性质

**类型族约束**：
```haskell
type family Elem x xs :: Bool where
  Elem x '[] = 'False
  Elem x (x ': xs) = 'True
  Elem x (y ': xs) = Elem x xs

class All p xs where
  proofAll :: Proxy p -> Proxy xs -> Dict (AllF p xs)

-- 编译时验证性质
insertPreservesAll :: (All p xs, p x) => 
  Proxy p -> x -> Vec xs -> Vec (x ': xs)
```

### 10.5.4 证明与测试的统一

**Curry-Howard对应**：
- 命题即类型
- 证明即程序
- 测试即证明搜索

**渐进验证**：
1. 快速性质测试
2. 有界模型检测
3. 完整证明（如果可能）

### 10.5.5 高级类型系统特性

**线性类型**：
- 资源使用性质
- 状态转换正确性
- 并发协议

**session类型**：
- 通信协议验证
- 死锁自由保证
- 进度性质

### 练习 10.5

1. 使用精化类型表达二分查找的前置条件。

<details>
<summary>参考答案</summary>

精化类型的二分查找：

```haskell
-- Liquid Haskell 规范
{-@ type SortedList a = [a]<{\x y -> x <= y}> @-}
{-@ type Index N = {v:Int | 0 <= v && v < N} @-}

{-@ binarySearch :: Ord a => 
      a -> 
      SortedList a -> 
      Maybe (Index (len xs))
@-}
binarySearch :: Ord a => a -> [a] -> Maybe Int
binarySearch x xs = go 0 (length xs - 1)
  where
    {-@ go :: lo:Nat -> 
              {hi:Int | lo <= hi + 1} -> 
              Maybe (Index (len xs)) 
    @-}
    go lo hi
      | lo > hi = Nothing
      | otherwise = 
          let mid = lo + (hi - lo) `div` 2
          in case compare x (xs !! mid) of
               LT -> go lo (mid - 1)
               GT -> go (mid + 1) hi
               EQ -> Just mid

-- 更强的规范：返回值的性质
{-@ binarySearchSpec :: Ord a => 
      x:a -> 
      xs:SortedList a -> 
      {r:Maybe (Index (len xs)) | 
        (isJust r => xs !! (fromJust r) == x) &&
        (isNothing r => not (elem x xs))
      }
@-}

-- 使用依赖类型（Idris风格）
binarySearch : Ord a => 
  (x : a) -> 
  (xs : Vect n a) -> 
  {auto prf : Sorted xs} ->
  Either (Not (Elem x xs)) (i : Fin n ** index i xs = x)

-- 辅助定义
data Sorted : Vect n a -> Type where
  SortedNil : Sorted []
  SortedOne : Sorted [x]
  SortedCons : {auto smaller : x <= y} ->
               Sorted (y :: ys) ->
               Sorted (x :: y :: ys)
```

这个规范：
- 编译时保证输入有序
- 返回索引保证有效
- 结果正确性编码在类型中
- 不可能返回错误结果
</details>

2. 设计一个结合类型和性质的验证框架。

<details>
<summary>参考答案</summary>

渐进式验证框架设计：

```haskell
-- 核心类型
data VerificationLevel = 
    Testing Int          -- 随机测试N个用例
  | Bounded Int         -- 有界验证深度N
  | Complete           -- 完整证明

data Property a = Property
  { propName :: String
  , propStatement :: a -> Bool
  , propGenerator :: Gen a
  , propPrecondition :: a -> Bool
  , propClassify :: a -> String
  }

-- 验证策略
class Verifiable prop where
  verify :: VerificationLevel -> prop -> VerificationResult
  
data VerificationResult = 
    Passed VerificationLevel Stats
  | Failed Counterexample
  | Unknown Reason

-- 类型级别编码
data Verified (p :: Symbol) a = Verified a

-- 智能构造函数
mkVerified :: forall p a. 
  (KnownSymbol p, Verifiable (Property a)) =>
  a -> Maybe (Verified p a)
mkVerified x = 
  case verify Complete (getProperty @p) of
    Passed _ _ -> Just (Verified x)
    _ -> Nothing

-- 组合验证
data a :&: b = a :&: b
infixr 6 :&:

instance (Verifiable a, Verifiable b) => 
         Verifiable (a :&: b) where
  verify level (a :&: b) = 
    case (verify level a, verify level b) of
      (Passed _ s1, Passed _ s2) -> 
        Passed level (combineStats s1 s2)
      (Failed c, _) -> Failed c
      (_, Failed c) -> Failed c
      (Unknown r, _) -> Unknown r
      (_, Unknown r) -> Unknown r

-- 使用示例
{-@ type PosList = Verified "all_positive" [Int] @-}

allPositive :: Property [Int]
allPositive = Property
  { propName = "all_positive"
  , propStatement = all (> 0)
  , propGenerator = listOf (choose (1, 100))
  , propPrecondition = const True
  , propClassify = \xs -> 
      if length xs < 10 then "small" else "large"
  }

-- 渐进式API
quickVerify :: Verifiable p => p -> IO Bool
quickVerify = fmap isPass . verify (Testing 100)

boundedVerify :: Verifiable p => Int -> p -> IO Bool  
boundedVerify n = fmap isPass . verify (Bounded n)

prove :: Verifiable p => p -> IO Bool
prove = fmap isPass . verify Complete

-- 条件编译
verifyLevel :: VerificationLevel
#ifdef RELEASE
verifyLevel = Complete
#else
verifyLevel = Testing 1000
#endif
```

框架特点：
- 统一的验证接口
- 可配置验证强度
- 类型安全的属性引用
- 渐进式验证策略
- 与构建系统集成
</details>

### 进一步研究

- 液体类型的自动推导
- 从测试生成类型标注
- 混合具体/符号执行
- 概率类型系统中的性质

## 10.6 Lambda立方体在测试中的应用

Lambda立方体提供了理解类型系统表达力的框架，这对设计测试策略有重要启发。

### 10.6.1 Lambda立方体回顾

**三个维度**：
1. **项依赖于项**（λ→）：简单类型lambda演算
2. **项依赖于类型**（λ2）：多态性
3. **类型依赖于类型**（λω）：类型算子
4. **类型依赖于项**（λP）：依赖类型

**八个系统**：
- λ→：简单类型
- λ2：System F
- λω：高阶类型
- λP：LF
- λP2：依赖多态
- λPω：高阶依赖
- λω_：弱高阶
- λC：构造演算

### 10.6.2 不同系统中的测试策略

**简单类型（λ→）**：
- 基于具体值的测试
- 类型保证基本安全
- 有限的多态性

**System F（λ2）**：
- 参数化性质
- 自由定理
- 泛型测试

**高阶类型（λω）**：
- 类型级别计算
- 更强的抽象
- 类型族测试

**依赖类型（λP）**：
- 规范即类型
- 证明即测试
- 完整验证

### 10.6.3 测试生成策略

**类型引导生成**：
```haskell
-- System F风格
genPoly :: forall f. 
  (forall a. Arbitrary a => Gen (f a)) ->
  Gen (forall a. f a)

-- 依赖类型风格  
genDependent :: 
  (n : Nat) -> Gen (Vec a n)
genDependent Zero = return Nil
genDependent (Succ n) = 
  Cons <$> arbitrary <*> genDependent n
```

### 10.6.4 性质的类型编码

**参数化性质**：
```haskell
-- 自由定理
freeTheorem :: 
  (forall a. [a] -> [a]) ->
  (forall a b. (a -> b) -> [a] -> [b])
freeTheorem f g = map g . f

-- 类型保证性质
data Balanced a = 
  Leaf a | 
  Node Int (Balanced a) (Balanced a)
  -- 高度差编码在类型中
```

### 10.6.5 实际应用

**渐进类型**：
- 动态测试到静态验证
- 可选的类型标注
- 混合验证策略

**契约系统**：
- 运行时类型检查
- 依赖契约
- 责备计算

### 练习 10.6

1. 展示如何在不同Lambda立方体系统中表达"排序列表"。

<details>
<summary>参考答案</summary>

不同系统中的排序列表：

```haskell
-- λ→ (简单类型)
-- 只能用约定，无法在类型中表达
newtype SortedList = SortedList [Int]
-- 需要智能构造函数保证

-- λ2 (System F)
-- 使用幻影类型
data Sorted
data Unsorted
newtype List s a = List [a]

sort :: Ord a => List Unsorted a -> List Sorted a
sort (List xs) = List (Data.List.sort xs)

-- 仍然依赖约定，但类型更精确

-- λω (高阶类型)
-- 使用类型级别列表
data Nat = Zero | Succ Nat
type family (<=) (m :: Nat) (n :: Nat) :: Bool

data SortedList (min :: Nat) a where
  SNil :: SortedList min a
  SCons :: (KnownNat n, min <= n ~ True) =>
           Proxy n -> a -> SortedList n a -> SortedList min a

-- λP (依赖类型 - Idris/Agda风格)
data SortedList : (a : Type) -> (Ordered a) -> Type where
  Nil : SortedList a ord
  Cons : (x : a) -> 
         (xs : SortedList a ord) ->
         {auto prf : AllGreaterEq x xs} ->
         SortedList a ord

-- 完整的依赖类型编码
SortedList : ∀ {A : Set} → 
            (R : A → A → Set) → 
            List A → Set
SortedList R [] = ⊤
SortedList R (x ∷ xs) = 
  All (R x) xs × SortedList R xs

-- λC (构造演算 - Coq风格)
Inductive sorted {A:Type} (R:A->A->Prop) : list A -> Prop :=
  | sorted_nil : sorted R nil
  | sorted_single : forall x, sorted R (x::nil)
  | sorted_cons : forall x y l,
      R x y -> sorted R (y::l) -> sorted R (x::y::l).

-- 使用类型类
Class Sorted {A:Type} (R:A->A->Prop) (l:list A) :=
  is_sorted : sorted R l.

-- 证明排序算法正确
Theorem sort_correct : forall l,
  Sorted le (sort l) /\ Permutation l (sort l).
```

不同系统的权衡：
- 简单类型：易理解，弱保证
- 多态：更通用，仍需约定
- 高阶：强类型，复杂度增加
- 依赖：完整规范，证明负担
</details>

2. 设计一个利用类型系统层级的测试框架。

<details>
<summary>参考答案</summary>

分层测试框架：

```haskell
-- 基础层：值级别测试
module Level0 where
  type Test a = a -> Bool
  
  runTest :: Show a => Test a -> a -> IO ()
  runTest test x = 
    putStrLn $ show x ++ ": " ++ 
    if test x then "PASS" else "FAIL"

-- 多态层：类型参数化测试  
module Level1 where
  class Testable a where
    type TestSpec a
    genTest :: TestSpec a -> Gen (Test a)
    
  -- 多态性质
  data PolyProp f = PolyProp
    { polyName :: String
    , polyProp :: forall a. (Arbitrary a, Show a) => 
                  f a -> Bool
    }

-- 高阶层：类型级别测试
module Level2 where
  -- 类型族测试
  type family TestResult (f :: * -> *) a :: Bool
  type instance TestResult [] Int = True
  type instance TestResult Maybe String = True
  
  -- 类型类法则测试
  class MonadLaws m where
    testReturn :: forall a. Eq a => 
                  a -> Bool
    testReturn x = 
      return x >>= return == return x
      
    testBind :: forall a b. (Eq b) =>
                a -> (a -> m b) -> Bool  
    testBind x f = 
      return x >>= f == f x

-- 依赖层：规范即测试
module Level3 where
  -- 依赖类型伪代码
  data Spec : (A : Type) -> (A -> Type) -> Type where
    Base : ∀ {A P} -> (∀ x -> Dec (P x)) -> Spec A P
    Refine : ∀ {A P Q} -> 
             Spec A P -> 
             Spec {x : A | P x} Q ->
             Spec A (λ x -> P x ∧ Q x)
             
  verify : ∀ {A P} -> Spec A P -> (x : A) -> Dec (P x)
  
  -- 自动生成测试
  deriveTests : ∀ {A P} -> Spec A P -> TestSuite A

-- 统一接口
module TestFramework where
  data TestLevel = Value | Poly | HigherOrder | Dependent
  
  class MultiLevelTest a where
    testLevel :: TestLevel
    runTests :: a -> TestReport
    
  -- 渐进式验证
  data VerificationPlan a = Plan
    { quickTests :: Level0.Test a
    , propTests :: Level1.PolyProp []
    , typeTests :: Level2.MonadLaws []
    , fullSpec :: Level3.Spec a IsValid
    }
    
  -- 根据可用资源选择级别
  selectLevel :: Resources -> VerificationPlan a -> IO ()
  selectLevel (Resources cpu time) plan
    | cpu < 10 = runLevel0 (quickTests plan)
    | cpu < 60 = runLevel1 (propTests plan)  
    | time < 300 = runLevel2 (typeTests plan)
    | otherwise = runLevel3 (fullSpec plan)
```

这个框架提供：
- 不同抽象级别的测试
- 渐进式验证策略
- 资源感知的测试选择
- 从具体到抽象的平滑过渡
</details>

### 进一步研究

- 立方体对角线上的混合系统
- 模态类型系统中的测试
- 线性逻辑与资源测试
- 同伦类型论中的路径测试

## 本章小结

基于性质的测试代表了测试方法论的重要进步，它将焦点从具体例子转向普遍规律。本章我们探讨了：

1. **思维转变**：从示例到性质需要抽象思维和规律发现能力
2. **技术基础**：生成器和缩小算法是PBT的核心技术
3. **状态处理**：有状态系统需要特殊的模型和验证技术
4. **工具生态**：QuickCheck及其衍生品形成了丰富的工具集
5. **类型集成**：与类型系统的结合提供了更强的保证
6. **理论深度**：Lambda立方体揭示了不同类型系统中的测试策略

PBT的关键优势：
- 自动发现边界情况
- 提高测试覆盖率
- 促进对系统的深入理解
- 与形式化方法的自然衔接

未来方向：
- 机器学习辅助的性质发现
- 分布式系统的性质测试
- 与证明助手的深度集成
- 领域特定的性质语言

下一章，我们将探讨规约挖掘与合成，看看如何自动发现和生成这些性质。