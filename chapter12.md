# 第12章：硬件和芯片测试

硬件测试与软件测试有着根本性差异：硬件制造过程中的物理缺陷、永久性故障以及量产需求都带来了独特挑战。芯片内包含数十亿个晶体管，如何高效检测制造缺陷并确保功能正确性，是一个兼具理论深度和实践价值的重要领域。本章将深入探讨硬件测试的理论基础、工程实践和前沿发展。

## 12.1 可测试性设计（DFT）

可测试性设计是在芯片设计阶段就考虑测试需求，通过增加额外的测试结构来提高故障检测能力和测试效率。

### 12.1.1 可测试性的基本概念

**可控制性（Controllability）**：
- 将电路内部节点设置为期望逻辑值的能力
- 通过输入信号控制内部状态
- 量化指标：SCOAP可控制性度量

**可观察性（Observability）**：
- 观察电路内部节点逻辑值的能力  
- 将内部信号传播到输出的能力
- 量化指标：SCOAP可观察性度量

**可测试性度量SCOAP**：
```
组合逻辑可控制性：
CC0(X) = min{CC0(inputs)} + 1  (AND门设0)
CC1(X) = sum{CC1(inputs)} + 1  (AND门设1)

时序逻辑可控制性：
考虑时钟和复位信号的额外代价

可观察性：
CO(X) = min{CO(fanouts)} + 1
```

### 12.1.2 扫描设计

**扫描链原理**：
- 将触发器连接成移位寄存器
- 测试模式下可直接控制和观察寄存器状态
- 大幅提高内部节点的可测试性

**扫描触发器结构**：
```
正常模式：D → Q
测试模式：扫描输入 → Q（通过多路选择器）
```

**全扫描设计优势**：
- 将时序电路测试转化为组合电路测试
- 故障覆盖率可达95%以上
- 测试向量生成简化

**部分扫描策略**：
- 只对关键触发器添加扫描功能
- 平衡测试效果与硬件开销
- 基于可测试性分析选择扫描点

### 12.1.3 测试点插入

**控制点（Control Point）**：
- 在低可控制性节点插入
- 通过额外的与门或或门
- 测试模式下强制节点为指定值

**观察点（Observation Point）**：
- 在低可观察性节点插入
- 将内部信号直接连接到输出
- 增加芯片管脚数量

**智能插入算法**：
- 基于可测试性梯度
- 考虑硬件开销约束
- 优化故障覆盖率提升

### 12.1.4 存储器测试设计

**存储器BIST**：
- 内建的测试算法
- 地址/数据/控制生成器
- 响应分析和压缩

**冗余修复**：
- 备用行列替换故障单元
- 可编程熔丝或反熔丝
- 提高成品率

### 12.1.5 时钟测试设计

**时钟域切换**：
- 测试时钟与功能时钟分离
- 可控的时钟速度
- 时钟门控测试

**延迟测试**：
- 过速时钟检测时序故障
- 时钟抖动容忍度
- 关键路径延迟测量

### 练习 12.1

1. 计算一个简单组合电路的SCOAP可测试性度量。

<details>
<summary>参考答案</summary>

SCOAP可测试性计算示例：

考虑电路：Z = A·B + C·D

```
       A ──┐
           ├── AND1 ──┐
       B ──┘          │
                      ├── OR ── Z
       C ──┐          │
           ├── AND2 ──┘
       D ──┘
```

**可控制性计算（从输入到输出）**：

初始化输入：
- CC0(A) = CC1(A) = 1
- CC0(B) = CC1(B) = 1  
- CC0(C) = CC1(C) = 1
- CC0(D) = CC1(D) = 1

AND1门（A·B）：
- CC0(AND1) = min{CC0(A), CC0(B)} + 1 = min{1,1} + 1 = 2
- CC1(AND1) = CC1(A) + CC1(B) + 1 = 1 + 1 + 1 = 3

AND2门（C·D）：
- CC0(AND2) = min{CC0(C), CC0(D)} + 1 = 2
- CC1(AND2) = CC1(C) + CC1(D) + 1 = 3

OR门（Z）：
- CC0(Z) = CC0(AND1) + CC0(AND2) + 1 = 2 + 2 + 1 = 5
- CC1(Z) = min{CC1(AND1), CC1(AND2)} + 1 = min{3,3} + 1 = 4

**可观察性计算（从输出到输入）**：

初始化输出：
- CO(Z) = 1

反向传播：
OR门到AND门：
- CO(AND1) = CO(Z) + CC0(AND2) + 1 = 1 + 2 + 1 = 4
- CO(AND2) = CO(Z) + CC0(AND1) + 1 = 1 + 2 + 1 = 4

AND门到输入：
- CO(A) = CO(AND1) + CC1(B) + 1 = 4 + 1 + 1 = 6
- CO(B) = CO(AND1) + CC1(A) + 1 = 4 + 1 + 1 = 6
- CO(C) = CO(AND2) + CC1(D) + 1 = 4 + 1 + 1 = 6  
- CO(D) = CO(AND2) + CC1(C) + 1 = 4 + 1 + 1 = 6

**可测试性分析**：
- 所有输入的可观察性相同，无特别难测试的节点
- Z的设0比设1困难（5 vs 4），符合OR门特性
- 总体可测试性良好，无需额外测试点
</details>

2. 设计一个4位计数器的扫描链结构。

<details>
<summary>参考答案</summary>

4位计数器扫描链设计：

**原始计数器结构**：
```
CLK ──┬─┬─┬─┬── (时钟信号)
      │ │ │ │
    ┌─▼─▼─▼─▼─┐
    │ FF0 FF1 FF2 FF3 │  (4个D触发器)
    └─┬─┬─┬─┬─┘
      │ │ │ │
Q[3:0]─┘ │ │ │
组合逻辑 ──┘ │ │  (计数逻辑)
           ┘ │
            ┘
```

**扫描触发器设计**：
```
每个触发器增加：
- 扫描输入端口 (SI)
- 扫描使能信号 (SE)
- 多路选择器

      SE
       │
   D ──┬── MUX ──┐
       │         │
   SI ─┘         ├── D触发器 ── Q
                 │
   CLK ──────────┘
```

**完整扫描链连接**：
```
SCAN_IN ── FF0.SI ── FF0.Q ── FF1.SI ── FF1.Q ── FF2.SI ── FF2.Q ── FF3.SI ── FF3.Q ── SCAN_OUT
           │                  │                  │                  │
           │                  │                  │                  │
       正常逻辑输入        正常逻辑输入        正常逻辑输入        正常逻辑输入
```

**控制信号**：
- SE=0：正常功能模式
- SE=1：扫描测试模式

**测试过程**：
1. **扫描载入阶段**：
   ```
   SE = 1  (切换到扫描模式)
   通过SCAN_IN串行载入测试向量：
   时钟1：载入FF0
   时钟2：载入FF1，FF0数据移至FF1
   时钟3：载入FF2，数据依次移位
   时钟4：载入FF3，完成4位数据载入
   ```

2. **功能执行阶段**：
   ```
   SE = 0  (切换到功能模式)
   时钟1次：执行一个计数周期
   观察组合逻辑行为
   ```

3. **扫描卸载阶段**：
   ```
   SE = 1  (切换回扫描模式)
   时钟4次：将结果串行移出
   在SCAN_OUT观察测试响应
   ```

**测试向量示例**：
```
测试计数功能：
载入：0000 → 期望：0001
载入：0001 → 期望：0010
载入：1111 → 期望：0000 (溢出)

测试组合逻辑故障：
载入：1010 → 检查特定逻辑门
载入：0101 → 交替模式测试
```

**优势**：
- 100%内部状态可控/可观
- 测试向量生成简化
- 可测试任意组合逻辑故障
- 支持延迟故障测试

**开销**：
- 每个FF增加1个2选1MUX
- 额外的扫描控制信号
- 约5-10%面积开销
- 扫描时间开销（4个时钟周期）
</details>

### 进一步研究

- 低功耗扫描设计技术
- 压缩扫描和X-masking
- 3D集成电路的测试挑战
- 人工智能在DFT优化中的应用

## 12.2 内建自测试（BIST）

内建自测试通过在芯片内部集成测试生成和响应分析电路，实现测试的自主化和高效化。

### 12.2.1 BIST基本架构

**核心组件**：
- 测试模式生成器（TPG）
- 待测电路（CUT）
- 响应分析器（RA）
- BIST控制器

**典型BIST流程**：
```
1. 初始化：复位所有BIST电路
2. 测试生成：TPG产生测试向量
3. 施加激励：将测试向量施加到CUT
4. 响应分析：RA分析CUT输出
5. 结果判断：比较期望与实际响应
```

### 12.2.2 伪随机测试生成

**线性反馈移位寄存器（LFSR）**：
- 生成伪随机序列
- 硬件实现简单
- 最大长度序列特性

**LFSR设计要点**：
```
n位LFSR可生成2^n-1长度序列
反馈多项式选择：
- 本原多项式保证最大周期
- 不同多项式产生不同序列

标准反馈多项式：
4位：x^4 + x + 1
8位：x^8 + x^4 + x^3 + x^2 + 1
16位：x^16 + x^12 + x^3 + x + 1
```

**种子依赖性问题**：
- 全0状态为吸收态
- 需要避免或处理全0种子
- 可采用修正的LFSR结构

**加权伪随机生成**：
- 针对特定故障的偏向生成
- 提高故障检测效率
- 平衡随机性与针对性

### 12.2.3 响应压缩技术

**多输入移位寄存器（MISR）**：
- 将多位响应压缩为固定长度
- 基于线性反馈移位寄存器
- 空间和时间双重压缩

**循环冗余码（CRC）**：
- 基于多项式除法
- 优秀的错误检测能力
- 标准化的生成多项式

**别名问题**：
- 错误响应被压缩为正确签名
- 别名概率：约2^(-n)，n为压缩位数
- 通过增加压缩长度降低风险

**时间压缩考虑**：
- 压缩序列与原始序列的关系
- 错误传播和累积效应
- 最优压缩策略

### 12.2.4 存储器BIST

**存储器故障模型**：
- 固定故障（SAF）：单元固定为0或1
- 转换故障（TF）：无法改变状态
- 耦合故障（CF）：单元间相互影响
- 地址故障：地址译码错误
- 数据保持故障：动态失效

**March算法家族**：
```
March C-：
{⇕(w0); ⇑(r0,w1); ⇑(r1,w0); ⇓(r0,w1); ⇓(r1,w0); ⇕(r0)}

符号说明：
⇑：地址递增
⇓：地址递减  
⇕：任意顺序
r0/r1：读0/读1
w0/w1：写0/写1
```

**算法复杂度对比**：
- March C-：11n（线性）
- March B：17n
- March A：15n
- GALPAT：n²（平方）

### 12.2.5 逻辑BIST设计

**随机抗性电路**：
- 某些电路对随机测试不敏感
- 需要特定的确定性向量
- 混合BIST策略

**测试点优化**：
- 提高随机测试效果
- 减少随机抗性
- 平衡硬件开销

**多阶段BIST**：
- 第一阶段：伪随机测试
- 第二阶段：确定性补充测试
- 针对剩余故障的特殊处理

### 练习 12.2

1. 设计一个8位LFSR的BIST系统并分析其覆盖率。

<details>
<summary>参考答案</summary>

8位LFSR BIST系统设计：

**LFSR结构**：
```
使用本原多项式：x^8 + x^4 + x^3 + x^2 + 1

8位LFSR连接：
┌─────────────────────────────────┐
│  ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐  │
└─▶│Q7├─│Q6├─│Q5├─│Q4├─│Q3├─│Q2├─│Q1├─│Q0├──┤
   └──┘ └──┘ └──┘ └─┬┘ └─┬┘ └─┬┘ └──┘ └──┘  │
                    │    │    │             │
                    └────┼────┼─────────────┘
                         │    │
                         └────┼─────────────┐
                              │             │
                              └─────────────┤
                                           XOR
```

**完整BIST系统**：
```
        ┌─────────────┐
        │ BIST控制器  │
        └─────┬───────┘
              │控制信号
    ┌─────────▼────────┐     ┌──────────────┐
    │   8位LFSR       │────▶│   待测电路    │
    │  (测试生成器)    │     │    (CUT)     │
    └──────────────────┘     └──────┬───────┘
                                    │
                             ┌──────▼───────┐
                             │   8位MISR    │
                             │ (响应分析器)  │
                             └──────┬───────┘
                                    │
                             ┌──────▼───────┐
                             │  比较器      │
                             │ (期望签名)   │
                             └──────────────┘
```

**MISR结构**：
```
使用相同的本原多项式进行响应压缩
输入来自CUT的多位输出，通过XOR网络反馈
```

**测试流程**：
```
1. 初始化：
   - LFSR种子：0x01 (避免全0)
   - MISR清零：0x00
   - 测试计数器：0

2. 测试循环 (重复255次)：
   for i = 1 to 255:
       pattern = LFSR.next()
       response = CUT.apply(pattern)
       MISR.compress(response)
       
3. 结果检查：
   signature = MISR.value
   if signature == expected_signature:
       PASS
   else:
       FAIL
```

**覆盖率分析**：

理论分析：
- 最大序列长度：2^8 - 1 = 255
- 8位输入空间：256种可能
- 覆盖率：255/256 = 99.6%
- 缺失：全0向量（通常不是问题）

实际考虑：
```python
# 故障覆盖率评估
def evaluate_coverage(circuit, fault_list):
    detected_faults = 0
    
    # 生成LFSR序列
    lfsr_patterns = generate_lfsr_sequence(seed=0x01, length=255)
    
    for fault in fault_list:
        fault_circuit = inject_fault(circuit, fault)
        
        for pattern in lfsr_patterns:
            good_response = circuit.simulate(pattern)
            fault_response = fault_circuit.simulate(pattern)
            
            if good_response != fault_response:
                detected_faults += 1
                break  # 故障已检测
    
    return detected_faults / len(fault_list)
```

典型覆盖率：
- 固定故障：95-98%
- 转换故障：90-95%
- 总体：93-97%

**优化策略**：
1. **多项式选择**：
   - 测试不同本原多项式
   - 选择覆盖率最高的

2. **种子优化**：
   ```
   # 尝试多个种子
   seeds = [0x01, 0x03, 0x05, 0x0F, 0x33, 0x55, 0xAA, 0xFF]
   best_coverage = 0
   for seed in seeds:
       coverage = evaluate_with_seed(seed)
       if coverage > best_coverage:
           best_seed = seed
           best_coverage = coverage
   ```

3. **混合方法**：
   - LFSR伪随机测试（主要）
   - 确定性向量补充（剩余故障）

**性能指标**：
- 硬件开销：约20-30个逻辑门
- 测试时间：255个时钟周期
- 故障覆盖率：93-97%
- 别名概率：< 2^(-8) = 0.39%
</details>

2. 比较不同存储器测试算法的效果和复杂度。

<details>
<summary>参考答案</summary>

存储器测试算法对比分析：

**1. MATS (Modified Algorithmic Test Sequence)**

算法：
```
{⇕(w0); ⇑(r0,w1); ⇓(r1,w0)}

步骤：
1. 写0到所有单元（任意顺序）
2. 读0写1，地址递增
3. 读1写0，地址递减
```

特性：
- 复杂度：4n
- 检测故障：固定故障、地址故障
- 优点：最简单、最快
- 缺点：故障覆盖有限

**2. March C-**

算法：
```
{⇕(w0); ⇑(r0,w1); ⇑(r1,w0); ⇓(r0,w1); ⇓(r1,w0); ⇕(r0)}

详细步骤：
1. 写0到所有位置（任意顺序）
2. 地址递增：读0，写1
3. 地址递增：读1，写0  
4. 地址递减：读0，写1
5. 地址递减：读1，写0
6. 读0（任意顺序）
```

特性：
- 复杂度：11n
- 检测故障：SAF、TF、大部分CF、AF
- 优点：广泛使用、平衡的复杂度/覆盖率
- 缺点：不能检测所有耦合故障

**3. March B**

算法：
```
{⇕(w0); ⇑(r0,w1,r1,w0,r0,w1); ⇑(r1,w0,w1); ⇓(r1,w0,w1,w0); ⇕(r0)}
```

特性：
- 复杂度：17n
- 检测故障：包括March C-的所有故障，plus更多CF
- 优点：更高的故障覆盖率
- 缺点：时间开销更大

**4. March A**

算法：
```
{⇕(w0); ⇑(r0,w1,r1,w0,r0,w1); ⇓(r1,w0,w1,w0); ⇕(r0)}
```

特性：
- 复杂度：15n
- 检测故障：类似March B但略少
- 平衡性：介于March C-和March B之间

**5. GALPAT (Galloping Pattern)**

算法：
```
for base_address in all_addresses:
    write 0 to all cells
    write 1 to base_address
    for other_address in all_other_addresses:
        read base_address (expect 1)
        read other_address (expect 0)
        write 1 to other_address
        read base_address (expect 1)
        read other_address (expect 1)
        write 0 to other_address
```

特性：
- 复杂度：O(n²)
- 检测故障：几乎所有类型，包括复杂耦合
- 优点：最高的故障检测能力
- 缺点：时间复杂度太高，实用性差

**故障检测能力对比表**：

| 故障类型 | MATS | March C- | March A | March B | GALPAT |
|---------|------|----------|---------|---------|---------|
| 固定故障(SAF) | ✓ | ✓ | ✓ | ✓ | ✓ |
| 转换故障(TF) | ✗ | ✓ | ✓ | ✓ | ✓ |
| 反转耦合(CFin) | ✗ | ✓ | ✓ | ✓ | ✓ |
| 幂等耦合(CFid) | ✗ | ✓ | ✓ | ✓ | ✓ |
| 状态耦合(CFst) | ✗ | 部分 | 部分 | ✓ | ✓ |
| 桥接故障(BF) | ✗ | 部分 | 部分 | ✓ | ✓ |
| 地址故障(AF) | ✓ | ✓ | ✓ | ✓ | ✓ |

**复杂度和时间对比**：

| 算法 | 时间复杂度 | 实际操作数 | 相对时间 |
|------|-----------|-----------|----------|
| MATS | 4n | 4n | 1× |
| March C- | 11n | 11n | 2.75× |
| March A | 15n | 15n | 3.75× |
| March B | 17n | 17n | 4.25× |
| GALPAT | n² | 4n²+2n | 1000×(n=1M) |

**选择策略**：

```python
def select_memory_test_algorithm(memory_size, time_budget, quality_requirement):
    if quality_requirement == "ULTRA_HIGH":
        if time_budget > memory_size * memory_size / 1000:
            return "GALPAT"
        else:
            return "March B"
    
    elif quality_requirement == "HIGH":
        return "March B" if time_budget > memory_size * 20 else "March A"
    
    elif quality_requirement == "MEDIUM":
        return "March C-"
    
    else:  # BASIC
        return "MATS"

# 混合策略
def hybrid_memory_test(memory):
    # 第一阶段：快速筛选
    if not run_mats(memory):
        return "FAIL_BASIC"
    
    # 第二阶段：标准测试
    if not run_march_c_minus(memory):
        return "FAIL_STANDARD"
    
    # 第三阶段：关键位置详细测试
    critical_addresses = identify_critical_addresses(memory)
    for addr in critical_addresses:
        if not run_galpat_local(memory, addr):
            return "FAIL_CRITICAL"
    
    return "PASS"
```

**新兴算法和技术**：

1. **透明BIST**：
   - 在正常操作期间进行测试
   - 不中断系统功能
   - 连续监控内存健康

2. **自适应算法**：
   - 根据发现的故障调整测试策略
   - 机器学习指导的测试生成
   - 实时故障概率评估

3. **并行测试**：
   - 多个内存块同时测试
   - 分区测试策略
   - 减少总测试时间

实践建议：
- 通用应用：March C-
- 高可靠性：March B
- 快速筛选：MATS
- 关键系统：分层混合策略
</details>

### 进一步研究

- 新兴存储技术的测试挑战
- 低功耗BIST设计
- 机器学习在测试优化中的应用
- 在线测试和自修复技术

## 12.3 边界扫描与JTAG

边界扫描是一种标准化的测试技术，通过IEEE 1149.1 JTAG标准，为电路板级和芯片级测试提供了统一的解决方案。

### 12.3.1 JTAG标准概述

**IEEE 1149.1标准**：
- 1990年发布的测试访问端口标准
- Joint Test Action Group的缩写
- 提供标准化的测试接口

**基本概念**：
- 在芯片的每个输入/输出管脚旁增加边界扫描单元
- 形成围绕芯片核心的扫描链
- 通过4线接口控制测试操作

**标准接口信号**：
- TCK（Test Clock）：测试时钟
- TMS（Test Mode Select）：模式选择
- TDI（Test Data In）：测试数据输入
- TDO（Test Data Out）：测试数据输出
- TRST（Test Reset）：测试复位（可选）

### 12.3.2 边界扫描架构

**边界扫描单元（BSC）**：
```
每个I/O引脚对应一个BSC，包含：
- 输入捕获触发器
- 输出控制触发器
- 三态控制触发器
- 多路选择器网络
```

**BSC工作模式**：
- 正常模式：信号正常传输
- 捕获模式：捕获引脚状态到扫描链
- 移位模式：扫描链数据移位
- 更新模式：将扫描数据施加到引脚

**典型BSC结构**：
```
核心输出 ──┬── MUX1 ── 输出引脚
          │
扫描链 ────┘

输入引脚 ──┬── MUX2 ── 核心输入
          │
          └── 捕获FF ── 扫描链
```

### 12.3.3 测试访问端口（TAP）

**TAP控制器状态机**：
- 16个状态的有限状态机
- 通过TMS信号控制状态转换
- 协调指令和数据的操作

**关键状态**：
```
Test-Logic-Reset：复位状态
Run-Test/Idle：空闲状态
Select-DR-Scan：选择数据寄存器
Capture-DR：捕获数据
Shift-DR：移位数据
Update-DR：更新输出
Select-IR-Scan：选择指令寄存器
```

**指令寄存器（IR）**：
- 存储当前测试指令
- 决定数据寄存器的连接
- 标准指令集和用户指令

### 12.3.4 标准测试指令

**BYPASS指令**：
- 最简单的测试指令
- 创建1位的数据路径
- 用于绕过不需要测试的器件

**SAMPLE/PRELOAD指令**：
- 采样所有边界扫描单元的当前值
- 预加载测试数据到输出单元
- 不干扰正常功能

**EXTEST指令**：
- 外部测试指令
- 控制和观察所有数字引脚
- 用于板级互连测试

**INTEST指令**：
- 内部测试指令
- 通过边界扫描访问内部逻辑
- 实现芯片内部的测试

### 12.3.5 板级测试应用

**互连测试**：
```
测试目标：
- 短路检测
- 开路检测  
- 桥接故障
- 引脚到引脚连接验证
```

**测试向量生成**：
- 基于网表信息
- 自动生成测试序列
- 故障字典方法

**诊断能力**：
- 精确定位故障位置
- 区分不同故障类型
- 提供修复指导

### 12.3.6 高级JTAG应用

**在系统编程（ISP）**：
- 通过JTAG接口编程Flash
- 固件更新和配置
- 制造阶段的编程

**调试支持**：
- 处理器调试接口
- 实时跟踪功能
- 断点和单步执行

**IEEE 1149.4扩展**：
- 模拟和混合信号测试
- 测试总线标准
- 模拟开关矩阵

### 练习 12.3

1. 设计一个简单的4引脚器件的JTAG边界扫描链。

<details>
<summary>参考答案</summary>

4引脚器件JTAG边界扫描设计：

**器件规格**：
```
器件：4位加法器
引脚：A[1:0], B[1:0], Sum[2:0], Carry_out
功能：Sum = A + B
```

**边界扫描单元分配**：
```
BSC0: A[0] (输入)
BSC1: A[1] (输入)  
BSC2: B[0] (输入)
BSC3: B[1] (输入)
BSC4: Sum[0] (输出)
BSC5: Sum[1] (输出)
BSC6: Sum[2] (输出)
BSC7: Carry_out (输出)
```

**JTAG接口**：
```
标准4线接口：
TCK  ── 测试时钟输入
TMS  ── 测试模式选择
TDI  ── 测试数据输入
TDO  ── 测试数据输出
```

**边界扫描链连接**：
```
TDI ── BSC0 ── BSC1 ── BSC2 ── BSC3 ── BSC4 ── BSC5 ── BSC6 ── BSC7 ── TDO
       │       │       │       │       │       │       │       │
       A[0]    A[1]    B[0]    B[1]   Sum[0]  Sum[1]  Sum[2]  Carry_out
```

**输入BSC结构（以A[0]为例）**：
```
              UpdateDR
                 │
   A[0]引脚 ──┬── │ ── 内核A[0]输入
             │   │
         ┌───▼───▼───┐
         │ 捕获FF    │ ── 扫描输出
         └───▲───────┘
             │
         CaptureDR
             
扫描输入 ───── 移位FF ────── 扫描输出
```

**输出BSC结构（以Sum[0]为例）**：
```
内核Sum[0] ──┬── MUX ──┬── Sum[0]引脚
            │       │
            │   ┌───▼───┐
            │   │更新FF │
            │   └───▲───┘
            │       │
            │   UpdateDR
            │
        ┌───▼───────┐
        │ 捕获FF    │ ── 扫描输出  
        └───▲───────┘
            │
        CaptureDR
        
扫描输入 ───── 移位FF ────── 扫描输出
```

**TAP控制器状态**：
```
Test-Logic-Reset (默认)
    │ TMS=0
    ▼
Run-Test/Idle
    │ TMS=1
    ▼
Select-DR-Scan
    │ TMS=0
    ▼
Capture-DR ── 捕获所有BSC当前值
    │ TMS=0
    ▼
Shift-DR ── 移位8次（8个BSC）
    │ TMS=1
    ▼
Update-DR ── 更新所有输出BSC
    │ TMS=0
    ▼
Run-Test/Idle
```

**指令寄存器定义**：
```
3位指令寄存器（支持8条指令）：

000: BYPASS   - 1位绕过寄存器
001: SAMPLE   - 采样所有边界单元
010: PRELOAD  - 预加载测试数据
011: EXTEST   - 外部测试（激活边界扫描）
100: INTEST   - 内部测试
101-111: 用户定义指令
```

**测试序列示例**：

1. **功能测试**：
```
步骤1：载入SAMPLE指令
TMS序列：1,1,0,0,0  (进入Shift-IR)
TDI数据：001        (SAMPLE指令)
TMS：1,1,0         (Update-IR)

步骤2：设置输入值A=01, B=10
TMS：1,0,0         (进入Capture-DR)
载入8位数据：00100100 (对应A[0]=0,A[1]=1,B[0]=0,B[1]=1)

步骤3：切换到EXTEST执行测试
步骤4：读取输出Sum和Carry
期望结果：Sum=011, Carry=0 (1+2=3)
```

2. **互连测试**：
```
测试A[0]到Sum[0]连接：
1. 载入EXTEST指令
2. A[0]=1, 其他输入=0
3. 检查Sum[0]=1（如果只有A[0]贡献）
4. 重复测试其他引脚
```

**边界扫描描述语言（BSDL）**：
```
entity ADDER4 is
port (
    A: in bit_vector(1 downto 0);
    B: in bit_vector(1 downto 0);
    Sum: out bit_vector(2 downto 0);
    Carry_out: out bit;
    
    TCK: in bit;
    TMS: in bit;
    TDI: in bit;
    TDO: out bit
);
use STD_1149_1_1990.all;

attribute INSTRUCTION_LENGTH of ADDER4: entity is 3;
attribute INSTRUCTION_OPCODE of ADDER4: entity is
    "BYPASS (000)," &
    "SAMPLE (001)," &
    "EXTEST (011)";

attribute BOUNDARY_LENGTH of ADDER4: entity is 8;
attribute BOUNDARY_REGISTER of ADDER4: entity is
    "0 (BC_1, A(0), input, X)," &
    "1 (BC_1, A(1), input, X)," &
    "2 (BC_1, B(0), input, X)," &
    "3 (BC_1, B(1), input, X)," &
    "4 (BC_1, Sum(0), output3, X, 8, 1, Z)," &
    "5 (BC_1, Sum(1), output3, X, 8, 1, Z)," &
    "6 (BC_1, Sum(2), output3, X, 8, 1, Z)," &
    "7 (BC_1, Carry_out, output3, X, 8, 1, Z)";
end ADDER4;
```

**测试覆盖率分析**：
- 引脚级短路/开路：100%
- 内部逻辑故障：取决于INTEST向量
- 互连故障：板级100%
- 时序故障：有限（准静态测试）
</details>

2. 分析JTAG在板级测试中的优势和限制。

<details>
<summary>参考答案</summary>

JTAG板级测试分析：

**优势分析**：

1. **标准化和互操作性**：
   ```
   优势：
   - IEEE 1149.1标准确保兼容性
   - 所有支持JTAG的器件可统一测试
   - 测试设备和软件标准化
   - 降低开发和维护成本
   
   实例：
   - 不同厂商的芯片可在同一测试系统中
   - 测试向量格式标准（SVF, STAPL）
   - ATE设备广泛支持
   ```

2. **非侵入式测试**：
   ```
   优势：
   - 不需要物理探针接触
   - 避免高频信号完整性问题
   - 可测试BGA、QFN等难接触封装
   - 减少测试治具复杂度
   
   对比传统ICT：
   传统：需要每个网络一个测试点
   JTAG：只需4-5个测试信号
   ```

3. **高故障诊断能力**：
   ```python
   # 故障定位精度
   class JTAGDiagnostics:
       def locate_fault(self, expected, actual):
           """精确到引脚级的故障定位"""
           fault_pins = []
           
           for pin_idx, (exp, act) in enumerate(zip(expected, actual)):
               if exp != act:
                   pin_info = self.get_pin_info(pin_idx)
                   fault_pins.append({
                       'pin': pin_info.name,
                       'net': pin_info.net,
                       'expected': exp,
                       'actual': act,
                       'fault_type': self.classify_fault(exp, act)
                   })
           
           return fault_pins
   
   # 故障分类
   def classify_fault(self, expected, actual):
       if expected == 1 and actual == 0:
           return "SHORT_TO_GND"
       elif expected == 0 and actual == 1:
           return "SHORT_TO_VCC"
       else:
           return "UNKNOWN"
   ```

4. **成本效益**：
   ```
   成本对比（相对于ICT）：
   - 测试治具成本：10-20%
   - 开发时间：30-50%
   - 维护成本：20-30%
   - 测试时间：50-80%（但测试范围不同）
   ```

**限制分析**：

1. **测试速度限制**：
   ```
   限制因素：
   - 串行扫描链：8位数据需要8个时钟
   - 典型频率：1-50MHz（远低于功能频率）
   - 大型器件扫描链很长（数千位）
   
   时间计算：
   scan_time = (boundary_length / frequency) * test_vectors
   
   实例：
   1000位边界链 @ 10MHz
   100个测试向量
   时间 = (1000/10M) * 100 = 10ms
   ```

2. **故障覆盖范围**：
   ```
   能检测的故障：
   ✓ 引脚间短路/开路
   ✓ 电源/地短路
   ✓ 互连故障
   ✓ 边界扫描单元故障
   
   不能检测的故障：
   ✗ 模拟电路故障
   ✗ 时序相关故障
   ✗ 功能逻辑故障（需要INTEST）
   ✗ 电源完整性问题
   ✗ 高频信号完整性
   ```

3. **器件依赖性**：
   ```
   限制：
   - 要求所有关键器件支持JTAG
   - 非JTAG器件的网络难以测试
   - 模拟器件通常不支持
   - 某些器件JTAG实现不完善
   
   解决方案：
   - 混合测试策略
   - 间接测试方法
   - 功能测试补充
   ```

4. **复杂性管理**：
   ```python
   # JTAG链管理复杂性
   class JTAGChainManager:
       def __init__(self, devices):
           self.devices = devices
           self.total_ir_length = sum(d.ir_length for d in devices)
           self.total_dr_length = {}  # 依赖于当前指令
       
       def load_instruction(self, device_id, instruction):
           """载入指令到特定器件"""
           # 需要计算每个器件在链中的位置
           # 其他器件载入BYPASS
           ir_data = self.build_ir_vector(device_id, instruction)
           self.shift_ir(ir_data)
       
       def build_ir_vector(self, target_device, instruction):
           """构建整个指令寄存器向量"""
           vector = []
           for device in self.devices:
               if device.id == target_device:
                   vector.extend(instruction)
               else:
                   vector.extend(device.bypass_instruction)
           return vector
   ```

**性能对比表**：

| 测试方面 | JTAG | ICT | 功能测试 | 飞针测试 |
|---------|------|-----|---------|----------|
| 互连覆盖 | 90-95% | 95-99% | 0-30% | 95-99% |
| 故障诊断 | 优秀 | 良好 | 一般 | 优秀 |
| 测试速度 | 慢 | 快 | 中等 | 慢 |
| 治具成本 | 低 | 高 | 中等 | 低 |
| 设置时间 | 短 | 长 | 中等 | 短 |
| 编程复杂度 | 中等 | 低 | 高 | 中等 |

**最佳应用场景**：

1. **适合JTAG的场景**：
   ```
   - 高密度SMT板卡
   - BGA封装器件较多
   - 多层板，内层信号多
   - 产品生命周期长
   - 成本敏感应用
   - 需要在线编程/调试
   ```

2. **不适合的场景**：
   ```
   - 纯模拟电路板
   - 极高频应用
   - 简单双面板
   - 一次性产品
   - 对测试时间极敏感
   ```

**混合测试策略**：
```python
def hybrid_test_strategy(board):
    results = {}
    
    # 第一阶段：JTAG互连测试
    jtag_result = jtag_interconnect_test(board)
    results['interconnect'] = jtag_result
    
    if not jtag_result.passed:
        return results  # 互连故障，无需继续
    
    # 第二阶段：功能测试
    func_result = functional_test(board)
    results['functional'] = func_result
    
    # 第三阶段：关键信号ICT测试
    critical_nets = identify_critical_nets(board)
    ict_result = ict_test(board, critical_nets)
    results['ict'] = ict_result
    
    return results
```

**结论**：
JTAG是板级测试的重要工具，特别适合现代高密度电路板。虽然有速度和覆盖范围的限制，但其标准化、成本效益和诊断能力使其成为测试策略的核心组件。最佳实践是将JTAG与其他测试方法结合，发挥各自优势。
</details>

### 进一步研究

- IEEE 1149.1的后续标准发展
- 高速信号的边界扫描技术
- 嵌入式仪器标准（IEEE 1149.4/.6/.7）
- JTAG在安全和调试中的应用

## 12.4 故障模型

硬件故障模型是测试向量生成和故障覆盖率评估的理论基础。不同的物理缺陷在逻辑层面表现为不同的故障模型。

### 12.4.1 固定故障模型

**单固定故障（Single Stuck-At Fault, SAF）**：
- 信号线固定为逻辑0（sa0）或逻辑1（sa1）
- 经典且最重要的故障模型
- 对应多种物理缺陷

**物理对应关系**：
- 金属线开路→输入sa0/sa1
- 晶体管漏极开路→输出sa0
- 电源短路→sa1
- 接地短路→sa0

**故障数量计算**：
```
n个信号线的电路：
单固定故障数 = 2n（每条线sa0和sa1）
假设：故障相互独立，单故障模型
```

**检测条件**：
为检测线路L的sa0故障：
1. 将L设置为1（激活）
2. 将故障效应传播到输出（传播）
3. 在输出观察到差异

### 12.4.2 桥接故障模型

**桥接故障定义**：
- 两条或多条信号线意外连接
- 反映实际制造中的金属桥接缺陷
- 比固定故障更真实

**桥接故障类型**：

1. **主导桥接（Dominant Bridging）**：
   - 一个信号主导另一个
   - 通常强驱动覆盖弱驱动

2. **线与桥接（Wired-AND）**：
   - 桥接结果为两信号的逻辑与
   - 任一信号为0，结果为0

3. **线或桥接（Wired-OR）**：
   - 桥接结果为两信号的逻辑或
   - 任一信号为1，结果为1

**桥接故障检测**：
```
检测A与B桥接：
1. 设置A=0, B=1（或相反）
2. 观察A和B的实际值
3. 如果都变为0（线与）或都变为1（线或），则检测到桥接
```

### 12.4.3 延迟故障模型

**延迟故障类型**：

1. **路径延迟故障（Path Delay Fault）**：
   - 整条路径延迟超过时钟周期
   - 反映路径上所有门的累积延迟

2. **转换延迟故障（Transition Delay Fault）**：
   - 单个门的延迟故障
   - 慢速上升（slow-to-rise）
   - 慢速下降（slow-to-fall）

3. **门延迟故障（Gate Delay Fault）**：
   - 特定门的输入到输出延迟异常
   - 可以是特定输入的延迟

**延迟故障检测**：
- 需要两个时间帧的向量对
- V1：初始化路径为稳定值
- V2：启动转换并在时钟边沿观察

**at-speed测试**：
- 使用功能时钟频率
- 检测实际工作条件下的时序故障
- 比静态测试更真实

### 12.4.4 IDDQ测试

**静态电流测试原理**：
- CMOS电路静态时电流应该很小（nA级）
- 某些故障导致异常电流（mA级）
- 通过测量电源电流检测故障

**可检测故障**：
- 栅极氧化层短路
- 漏极/源极桥接
- 某些固定故障
- 亚阈值泄漏

**IDDQ测试挑战**：
- 工艺技术缩小导致泄漏电流增大
- 深亚微米工艺中应用受限
- 需要特殊的测试设备

### 12.4.5 存储器故障模型

**单元故障**：
- 固定故障：单元固定为0或1
- 转换故障：无法从0变1或从1变0
- 数据保持故障：动态失效

**耦合故障**：
- 反转耦合：一个单元影响另一个单元状态
- 幂等耦合：写操作影响邻近单元
- 状态耦合：读操作影响其他单元

**地址故障**：
- 地址译码器故障
- 访问错误单元
- 多个单元同时被选中

### 练习 12.4

1. 设计测试向量检测一个2输入与门的所有固定故障。

<details>
<summary>参考答案</summary>

2输入与门固定故障分析：

**电路：Z = A · B**

```
A ──┐
    ├── AND ── Z
B ──┘
```

**故障列表**：
```
1. A sa0 (输入A固定为0)
2. A sa1 (输入A固定为1)
3. B sa0 (输入B固定为0)
4. B sa1 (输入B固定为1)
5. Z sa0 (输出Z固定为0)
6. Z sa1 (输出Z固定为1)
```

**故障检测分析**：

1. **A sa0故障**：
   - 故障电路：Z = 0 · B = 0
   - 正常电路：Z = A · B
   - 检测条件：需要A=1，且使正常输出≠0
   - 检测向量：A=1, B=1 → 正常输出Z=1，故障输出Z=0

2. **A sa1故障**：
   - 故障电路：Z = 1 · B = B
   - 正常电路：Z = A · B
   - 检测条件：需要A=0，使A·B≠B
   - 检测向量：A=0, B=1 → 正常输出Z=0，故障输出Z=1

3. **B sa0故障**：
   - 故障电路：Z = A · 0 = 0
   - 检测向量：A=1, B=1 → 正常输出Z=1，故障输出Z=0

4. **B sa1故障**：
   - 故障电路：Z = A · 1 = A
   - 检测向量：A=1, B=0 → 正常输出Z=0，故障输出Z=1

5. **Z sa0故障**：
   - 故障电路：Z = 0（无论输入如何）
   - 检测条件：正常输出为1
   - 检测向量：A=1, B=1 → 正常输出Z=1，故障输出Z=0

6. **Z sa1故障**：
   - 故障电路：Z = 1（无论输入如何）
   - 检测条件：正常输出为0
   - 检测向量：A=0, B=0 → 正常输出Z=0，故障输出Z=1
   - 或者：A=0, B=1 → 正常输出Z=0，故障输出Z=1
   - 或者：A=1, B=0 → 正常输出Z=0，故障输出Z=1

**测试向量集合**：

完整测试向量（4个向量，覆盖所有故障）：
```
向量1：A=0, B=0 → Z=0  [检测 Z sa1]
向量2：A=0, B=1 → Z=0  [检测 A sa1, Z sa1]
向量3：A=1, B=0 → Z=0  [检测 B sa1, Z sa1]
向量4：A=1, B=1 → Z=1  [检测 A sa0, B sa0, Z sa0]
```

**最小测试向量集**：

分析哪些向量是必需的：
```
- 检测输入sa0：需要该输入为1且输出为1
  → 必须有A=1,B=1
  
- 检测输入sa1：需要该输入为0且输出为0
  → 必须有A=0,B=1或A=1,B=0（任选一个）
  
- 检测输出sa1：需要正常输出为0
  → 可用A=0,B=0或A=0,B=1或A=1,B=0
```

最小向量集（3个向量）：
```
向量1：A=0, B=1 → Z=0  [检测 A sa1, Z sa1]
向量2：A=1, B=0 → Z=0  [检测 B sa1, Z sa1]  
向量3：A=1, B=1 → Z=1  [检测 A sa0, B sa0, Z sa0]
```

**故障覆盖表**：

| 向量 | A | B | Z正常 | A sa0 | A sa1 | B sa0 | B sa1 | Z sa0 | Z sa1 |
|------|---|---|-------|-------|-------|-------|-------|-------|-------|
| V1   | 0 | 1 | 0     | -     | ✓     | -     | ✓     | -     | ✓     |
| V2   | 1 | 0 | 0     | -     | -     | -     | ✓     | -     | ✓     |  
| V3   | 1 | 1 | 1     | ✓     | -     | ✓     | -     | ✓     | -     |

**验证**：
```python
def verify_fault_coverage():
    test_vectors = [(0,1), (1,0), (1,1)]
    faults = ['A_sa0', 'A_sa1', 'B_sa0', 'B_sa1', 'Z_sa0', 'Z_sa1']
    
    def and_gate(a, b):
        return a & b
    
    def faulty_circuit(a, b, fault):
        if fault == 'A_sa0': a = 0
        elif fault == 'A_sa1': a = 1
        elif fault == 'B_sa0': b = 0
        elif fault == 'B_sa1': b = 1
        
        z = and_gate(a, b)
        
        if fault == 'Z_sa0': z = 0
        elif fault == 'Z_sa1': z = 1
        
        return z
    
    coverage = {}
    for fault in faults:
        detected = False
        for a, b in test_vectors:
            normal_output = and_gate(a, b)
            faulty_output = faulty_circuit(a, b, fault)
            if normal_output != faulty_output:
                detected = True
                break
        coverage[fault] = detected
    
    return coverage

# 结果：所有故障都被检测到
print(verify_fault_coverage())
# {'A_sa0': True, 'A_sa1': True, 'B_sa0': True, 'B_sa1': True, 'Z_sa0': True, 'Z_sa1': True}
```

**通用结论**：
- 与门的完整故障检测需要至少3个向量
- 包含真值表中能产生1的输入组合（检测sa0故障）
- 包含能产生0的输入组合（检测sa1故障）
- 每个输入都要在0和1状态下测试
</details>

2. 分析为什么延迟故障比固定故障更难检测。

<details>
<summary>参考答案</summary>

延迟故障检测困难性分析：

**1. 检测条件复杂性**

固定故障检测：
```
条件简单：
- 激活故障（设置故障点为指定值）
- 传播到输出（使差异可观察）
- 单个向量即可

示例：检测线路L的sa0
向量：设置L=1，传播路径为敏感
```

延迟故障检测：
```
条件复杂：
- 需要两个向量的序列（V1, V2）
- V1：初始化，设置路径为稳定值
- V2：启动转换，在时钟边沿检测
- 还需考虑时序约束

示例：检测路径P的慢速上升
V1：设置路径输入为0（稳定）
V2：设置路径输入为1，期望输出在时钟边沿前到达
```

**2. 路径敏化问题**

固定故障：
```python
def sensitize_path_for_SAF(circuit, fault_line):
    """为固定故障敏化路径"""
    # 只需要设置侧向输入为非控制值
    # 相对简单，路径数量有限
    
    path = find_path_to_output(fault_line)
    for gate in path:
        set_side_inputs_non_controlling(gate)
    return True  # 通常可以找到敏化路径
```

延迟故障：
```python
def sensitize_path_for_delay(circuit, path, v1, v2):
    """为延迟故障敏化路径"""
    # 需要考虑：
    # 1. 路径在V1下稳定
    # 2. 路径在V2下敏化
    # 3. 其他路径不能干扰
    # 4. 时序窗口内只有目标路径切换
    
    # 检查V1稳定性
    if not is_path_stable(circuit, path, v1):
        return False
    
    # 检查V2敏化
    if not is_path_sensitized(circuit, path, v1, v2):
        return False
    
    # 检查竞争
    competing_paths = find_competing_paths(circuit, path)
    for cp in competing_paths:
        if path_switches(circuit, cp, v1, v2):
            return False  # 竞争路径干扰
    
    return True
```

**3. 时序复杂性**

固定故障（静态）：
```
特点：
- 时间无关，逻辑级分析
- 不需要考虑延迟
- 任何时钟频率下都有效

测试：
- 慢速测试即可
- 不需要精确时序
- 功能级验证
```

延迟故障（动态）：
```
复杂性：
- 必须使用at-speed测试
- 延迟值是模拟量，不是离散的
- 工艺变化影响延迟分布
- 温度、电压影响延迟

挑战：
- 测试设备时序精度要求高
- 时钟偏斜影响测试结果
- 建立/保持时间约束
- jitter和噪声影响
```

**4. 故障传播问题**

固定故障传播：
```
传播机制：
- 逻辑值差异传播
- 确定性的逻辑运算
- 可以通过多个门级联传播

示例：
门1输入差异 → 门1输出差异 → 门2输出差异 → ... → 主输出差异
```

延迟故障传播：
```python
class DelayFaultPropagation:
    def propagate_delay_fault(self, circuit, fault_path, delay_fault):
        """延迟故障传播分析"""
        
        # 1. 时序窗口分析
        nominal_delay = self.calculate_path_delay(circuit, fault_path)
        fault_delay = nominal_delay + delay_fault.extra_delay
        
        # 2. 检查是否违反时序约束
        clock_period = circuit.clock_period
        setup_time = circuit.setup_time
        
        if fault_delay > (clock_period - setup_time):
            return "TIMING_VIOLATION"  # 可检测
        else:
            return "NO_VIOLATION"     # 不可检测
    
    def analyze_delay_masking(self, circuit, fault_path):
        """分析延迟掩盖效应"""
        
        # 逻辑掩盖：其他输入变化掩盖延迟效应
        logic_masking = self.check_logic_masking(circuit, fault_path)
        
        # 时序掩盖：后续路径延迟掩盖故障
        timing_masking = self.check_timing_masking(circuit, fault_path)
        
        # 电气掩盖：驱动能力掩盖小延迟
        electrical_masking = self.check_electrical_masking(circuit, fault_path)
        
        return {
            'logic': logic_masking,
            'timing': timing_masking, 
            'electrical': electrical_masking
        }
```

**5. 向量生成复杂度**

固定故障ATPG：
```
算法复杂度：
- D算法：O(2^n) 最坏情况
- FAN算法：启发式，实践中高效
- 可达性好，收敛快

成功率：
- 通常>95%的故障可生成向量
- 算法成熟，工具可靠
```

延迟故障ATPG：
```python
class DelayFaultATPG:
    def generate_delay_vectors(self, circuit, delay_fault):
        """延迟故障向量生成"""
        
        # 搜索空间更大：需要考虑向量对(V1,V2)
        search_space = len(circuit.inputs) ** 4  # 比SAF大得多
        
        # 约束更多
        constraints = [
            self.stabilization_constraint(),  # V1稳定约束
            self.sensitization_constraint(),  # 路径敏化约束
            self.propagation_constraint(),    # 传播约束
            self.timing_constraint()          # 时序约束
        ]
        
        # 成功率更低
        generation_success_rate = 0.7  # 低于SAF的0.95
        
        return self.constraint_solve(search_space, constraints)
```

**6. 测试成本**

固定故障测试：
```
成本因素：
- 低速测试设备即可
- 测试时间较短
- 向量数量相对较少
- 一次性测试

典型成本：基准1x
```

延迟故障测试：
```
成本因素：
- 需要高速测试设备（昂贵）
- at-speed时钟生成复杂
- 向量对比单向量多
- 可能需要多个频率测试
- 温度/电压变化测试

典型成本：5-10x基准成本
```

**7. 诊断复杂性**

固定故障诊断：
```python
def diagnose_SAF(failing_vectors, fault_dictionary):
    """固定故障诊断相对简单"""
    suspects = []
    
    for fault in fault_dictionary:
        if fault.response_matches(failing_vectors):
            suspects.append(fault)
    
    # 通常可以精确定位到几个候选故障
    return suspects
```

延迟故障诊断：
```python
def diagnose_delay_fault(timing_failures, process_variations):
    """延迟故障诊断复杂"""
    
    # 1. 区分真实故障vs工艺变化
    real_faults = []
    process_outliers = []
    
    for failure in timing_failures:
        if failure.delay_amount > process_variations.threshold:
            real_faults.append(failure)
        else:
            process_outliers.append(failure)
    
    # 2. 多个路径可能共享同一个慢门
    # 需要路径交集分析
    common_gates = self.find_common_elements(real_faults)
    
    # 3. 考虑时序相关性
    # 一个门的延迟可能影响多条路径
    
    return self.correlate_timing_failures(common_gates)
```

**结论**：

延迟故障检测困难的根本原因：
1. **维度增加**：从空间（逻辑）扩展到时间（时序）
2. **约束复杂**：多个相互关联的约束条件
3. **连续性**：延迟是连续参数，不是离散逻辑值
4. **工艺敏感**：受制造工艺变化影响大
5. **设备要求**：需要复杂昂贵的测试设备

这解释了为什么业界仍以固定故障为主要测试目标，延迟故障测试主要用于关键应用和高性能电路。
</details>

### 进一步研究

- 纳米工艺中的新兴故障模型
- 软错误和单粒子翻转
- 老化相关的故障机制
- 机器学习在故障建模中的应用

## 12.5 自动测试图案生成（ATPG）

自动测试图案生成是硬件测试的核心技术，通过算法自动生成能够检测特定故障的测试向量。

### 12.5.1 ATPG问题定义

**基本问题**：
给定电路和故障列表，自动生成测试向量集合，使得：
- 最大化故障覆盖率
- 最小化测试向量数量
- 满足时间和计算资源约束

**问题复杂性**：
- NP完全问题
- 搜索空间：2^n（n为输入数）
- 需要启发式算法

### 12.5.2 D算法

**基本思想**：
- 将故障激活和传播问题转化为逻辑约束求解
- 使用D代数扩展常规逻辑
- 系统化搜索测试向量

**D代数**：
- 0, 1：正常逻辑值
- D：正常为1，故障为0
- D̄：正常为0，故障为1
- X：未知值

**D算法步骤**：
1. **故障激活**：在故障位置产生D或D̄
2. **D传播**：将D值传播到主输出
3. **线路赋值**：设置其他输入以保证传播
4. **一致性检查**：验证赋值无矛盾

**D传播规则**：
```
AND门：
1 · D = D
0 · D = 0
X · D = X

OR门：
0 + D = D  
1 + D = 1
X + D = X

NOT门：
¬D = D̄
¬D̄ = D
```

### 12.5.3 FAN算法

**改进动机**：
- D算法回溯次数过多
- 需要更智能的搜索策略
- 提高算法效率

**关键改进**：

1. **多重回溯**：
   - 同时尝试多个赋值
   - 避免过早的错误决策
   - 减少回溯深度

2. **唯一敏化**：
   - 优先选择唯一敏化路径
   - 减少搜索分支
   - 提高成功概率

3. **头线识别**：
   - 找出影响多个目标的关键线路
   - 优先处理头线
   - 加速收敛

**FAN算法流程**：
```
1. 初始化：设置故障激活目标
2. 目标选择：选择当前最重要的目标
3. 回溯点选择：选择最有希望的回溯点
4. 赋值决策：进行局部赋值
5. 蕴含操作：传播赋值的影响
6. 检查矛盾：验证一致性
7. 重复或回溯：直到找到解或证明无解
```

### 12.5.4 基于SAT的ATPG

**SAT建模优势**：
- 将ATPG问题转化为布尔可满足性问题
- 利用现代SAT求解器的强大能力
- 处理复杂约束和优化目标

**编码方法**：

1. **电路结构编码**：
```
对每个门g：
输入：x1, x2, ..., xn
输出：y

AND门：y ↔ (x1 ∧ x2 ∧ ... ∧ xn)
OR门：y ↔ (x1 ∨ x2 ∨ ... ∨ xn)  
NOT门：y ↔ ¬x1
```

2. **故障效应编码**：
```
对于线路L的sa0故障：
引入故障变量Lf
约束：Lf = 0

正常输出：On
故障输出：Of
检测条件：On ≠ Of
```

3. **时间帧展开**：
```
对于时序电路：
时间帧0：初始状态和输入
时间帧1：时钟后的状态
...
直到故障效应传播到输出
```

### 12.5.5 压缩测试

**动机**：
- 测试向量数量巨大
- 测试时间和存储成本高
- 需要减少测试数据量

**压缩技术**：

1. **测试向量压缩**：
   - 线性反馈移位寄存器（LFSR）
   - 种子压缩
   - 统计编码

2. **响应压缩**：
   - 多输入移位寄存器（MISR）
   - 循环冗余码（CRC）
   - 时间和空间压缩

3. **X值处理**：
   - 未知值影响压缩效果
   - X-masking技术
   - X-tolerant压缩

**压缩比计算**：
```
压缩比 = 原始数据量 / 压缩后数据量

典型值：
测试向量：50:1 - 100:1
测试响应：1000:1 - 10000:1
```

### 练习 12.5

1. 使用D算法为一个简单电路生成测试向量。

<details>
<summary>参考答案</summary>

D算法测试向量生成示例：

**目标电路**：
```
       A ──┐
           ├── G1(AND) ── E ──┐
       B ──┘                 │
                             ├── G3(OR) ── Z
       C ──┐                 │
           ├── G2(AND) ── F ──┘
       D ──┘
```

逻辑表达式：Z = (A·B) + (C·D) = E + F

**目标故障**：E线路sa0 (E stuck-at 0)

**D算法求解过程**：

**步骤1：故障激活**
- 故障：E sa0
- 正常情况：E = A·B  
- 故障情况：E = 0
- 激活条件：使A·B = 1，即A=1, B=1
- 故障激活后：E正常=1, E故障=0，表示为E=D

当前赋值：A=1, B=1, E=D

**步骤2：D传播**
- 目标：将E的D值传播到输出Z
- Z = E + F = D + F
- 传播条件：需要F不能掩盖D
- 对于OR门，要传播D，需要F=0
- 因此设置：F = 0

更新赋值：A=1, B=1, E=D, F=0

**步骤3：确定F=0的条件**
- F = C·D = 0
- 满足条件：C=0 或 D=0（或两者都为0）
- 选择：C=0, D=X（D可以是任意值）

更新赋值：A=1, B=1, C=0, D=X, E=D, F=0

**步骤4：计算输出值**
- Z = E + F = D + 0 = D
- 正常电路：Z = 1
- 故障电路：Z = 0
- 检测成功！

**最终测试向量**：
```
A=1, B=1, C=0, D=0 (选择D=0)

验证：
正常电路：
- E = A·B = 1·1 = 1
- F = C·D = 0·0 = 0
- Z = E + F = 1 + 0 = 1

故障电路(E sa0)：
- E = 0 (固定)
- F = C·D = 0·0 = 0
- Z = E + F = 0 + 0 = 0

输出差异：1 ≠ 0，故障被检测到
```

**D算法详细追踪表**：

| 步骤 | 操作 | A | B | C | D | E | F | Z | 备注 |
|------|------|---|---|---|---|---|---|---|------|
| 0 | 初始 | X | X | X | X | X | X | X | 全部未知 |
| 1 | 激活E sa0 | 1 | 1 | X | X | D | X | X | A·B=1产生D |
| 2 | 传播到Z | 1 | 1 | X | X | D | 0 | X | F=0确保传播 |
| 3 | 确定F=0 | 1 | 1 | 0 | X | D | 0 | X | C=0使F=0 |
| 4 | 计算输出 | 1 | 1 | 0 | 0 | D | 0 | D | D传播到输出 |

**其他可能的解**：
```
由于D可以是任意值，其他有效解包括：
- A=1, B=1, C=0, D=1
- A=1, B=1, C=1, D=0  
- A=1, B=1, C=X, D=0（如果允许C未定义）

但最简单的解是：A=1, B=1, C=0, D=0
```

**算法特点总结**：
1. **系统性**：D算法提供了系统化的搜索方法
2. **完备性**：如果存在测试向量，D算法最终能找到
3. **复杂性**：对于大电路，搜索空间仍然很大
4. **优化空间**：可以通过启发式改进（如FAN算法）

**扩展：检测其他故障**：

对于F线路sa1故障：
```
故障激活：C=1, D=1 使F=1，故障后F=1，无差异
需要F=0，故障后F=1，表示为F=D̄
激活条件：C=0或D=0，使F=0
传播条件：E=0确保F的影响传播
测试向量：A=0, B=X, C=1, D=1
```

这个例子展示了D算法的核心思想：故障激活→差异传播→一致性求解。
</details>

2. 比较传统ATPG和基于SAT的ATPG方法。

<details>
<summary>参考答案</summary>

传统ATPG vs SAT-based ATPG对比分析：

**1. 算法基础**

传统ATPG（D算法/FAN）：
```
基础：专用搜索算法
特点：
- 直接在电路图上操作
- 使用领域特定启发式
- 深度优先搜索 + 回溯
- 手工优化的数据结构

优势：
- 针对硬件电路优化
- 启发式高效
- 内存使用可控
```

SAT-based ATPG：
```
基础：布尔可满足性求解
特点：
- 将问题转化为CNF
- 使用通用SAT求解器
- 冲突驱动的学习
- 现代SAT算法优化

优势：
- 算法持续改进
- 处理复杂约束能力强
- 自动学习和优化
```

**2. 问题建模方式**

传统方法：
```python
class TraditionalATPG:
    def __init__(self, circuit, fault):
        self.circuit = circuit
        self.fault = fault
        self.assignment = {}
        
    def solve(self):
        # 直接在电路上搜索
        self.activate_fault()
        self.propagate_fault_effect()
        self.justify_assignments()
        return self.assignment
    
    def activate_fault(self):
        """在故障位置产生差异"""
        fault_line = self.fault.line
        if self.fault.type == 'sa0':
            self.set_value(fault_line, 1)  # 激活sa0
        else:
            self.set_value(fault_line, 0)  # 激活sa1
    
    def propagate_fault_effect(self):
        """将差异传播到输出"""
        for gate in self.get_propagation_path():
            self.sensitize_gate(gate)
```

SAT方法：
```python
class SATBasedATPG:
    def __init__(self, circuit, fault):
        self.circuit = circuit
        self.fault = fault
        self.cnf = CNF()
        
    def solve(self):
        # 构建SAT实例
        self.encode_circuit()
        self.encode_fault()
        self.encode_detection_condition()
        
        # 调用SAT求解器
        result = self.sat_solver.solve(self.cnf)
        return self.extract_test_vector(result)
    
    def encode_circuit(self):
        """将电路编码为CNF"""
        for gate in self.circuit.gates:
            if gate.type == 'AND':
                self.encode_and_gate(gate)
            elif gate.type == 'OR':
                self.encode_or_gate(gate)
    
    def encode_and_gate(self, gate):
        """AND门的CNF编码"""
        inputs = gate.inputs
        output = gate.output
        
        # output -> (input1 & input2 & ...)
        # 等价于：¬output ∨ (input1 ∧ input2 ∧ ...)
        # CNF形式：(¬output ∨ input1) ∧ (¬output ∨ input2) ∧ ...
        for inp in inputs:
            self.cnf.add_clause([-output, inp])
            
        # (input1 & input2 & ...) -> output  
        # 等价于：¬(input1 ∧ input2 ∧ ...) ∨ output
        # CNF形式：(¬input1 ∨ ¬input2 ∨ ... ∨ output)
        clause = [-inp for inp in inputs] + [output]
        self.cnf.add_clause(clause)
```

**3. 处理复杂性能力对比**

传统ATPG局限性：
```
1. 复杂约束处理困难：
   - 时序约束
   - 功耗约束
   - X值处理
   
2. 扩展性问题：
   - 启发式难以泛化
   - 新的电路结构需要新启发式
   - 维护成本高

3. 优化目标单一：
   - 主要关注故障检测
   - 难以同时优化多个目标
```

SAT-based优势：
```python
class AdvancedSATATPG:
    def multi_objective_optimization(self):
        """多目标优化"""
        # 同时优化：故障覆盖、向量数量、功耗
        for objective in ['coverage', 'vectors', 'power']:
            self.add_objective_constraints(objective)
    
    def handle_timing_constraints(self):
        """处理时序约束"""
        # 添加时序相关的CNF子句
        for path in self.circuit.critical_paths:
            self.add_timing_clauses(path)
    
    def x_value_handling(self):
        """X值处理"""
        # 通过约束消除X值的影响
        for unknown_line in self.x_lines:
            self.add_x_masking_constraints(unknown_line)
```

**4. 性能比较**

运行时间：
```
电路规模        传统ATPG    SAT-based
小规模(<1K门)      快          慢
中规模(1K-10K)     中等        中等  
大规模(>10K)       慢/失败      快
复杂约束           失败        适中
```

内存使用：
```
传统ATPG：
- 电路表示：紧凑
- 搜索状态：较少
- 总体：低内存

SAT-based：
- CNF表示：冗余较多
- 学习子句：增长
- 总体：高内存
```

**5. 实际应用对比**

工业应用统计：
```
方法           市场份额    应用场景
传统ATPG        60%       成熟电路、快速测试
SAT-based      30%       复杂电路、研究
混合方法        10%       高端应用

趋势：SAT-based份额逐年增加
```

**6. 混合方案**

现代商业工具通常采用混合策略：
```python
class HybridATPG:
    def __init__(self, circuit, faults):
        self.circuit = circuit
        self.faults = faults
        
    def solve(self):
        results = {}
        
        # 第一阶段：传统算法处理简单故障
        simple_faults = self.classify_simple_faults()
        for fault in simple_faults:
            if self.time_budget_remaining() > threshold:
                result = self.traditional_solve(fault)
                results[fault] = result
            else:
                break
        
        # 第二阶段：SAT处理剩余困难故障
        remaining_faults = set(self.faults) - set(results.keys())
        for fault in remaining_faults:
            result = self.sat_solve(fault)
            results[fault] = result
            
        return results
    
    def classify_simple_faults(self):
        """识别适合传统方法的故障"""
        simple = []
        for fault in self.faults:
            if (self.get_fault_depth(fault) < 10 and
                self.get_fanout_cone_size(fault) < 100):
                simple.append(fault)
        return simple
```

**7. 未来发展趋势**

技术融合：
```
1. 机器学习增强：
   - 学习最优启发式
   - 预测SAT求解难度
   - 智能算法选择

2. 并行化：
   - GPU加速SAT求解
   - 分布式ATPG
   - 故障并行处理

3. 近似算法：
   - 快速近似解
   - 渐进精化
   - 实时约束满足
```

**选择建议**：

| 场景 | 推荐方法 | 理由 |
|------|----------|------|
| 快速原型 | 传统ATPG | 工具成熟，速度快 |
| 复杂约束 | SAT-based | 约束处理能力强 |
| 大规模电路 | 混合方法 | 平衡效率和能力 |
| 研究新算法 | SAT-based | 易于扩展和实验 |
| 产品化工具 | 混合方法 | 覆盖所有应用场景 |

总结：传统ATPG和SAT-based方法各有优势，现代趋势是智能融合两者，根据具体问题特征选择最适合的方法。
</details>

### 进一步研究

- 量子计算在ATPG中的应用
- 机器学习辅助的测试向量优化
- 安全性意识的测试生成
- 低功耗测试的约束满足

## 本章小结

硬件和芯片测试代表了测试技术的高度工程化应用。本章我们探讨了：

1. **可测试性设计**：通过设计阶段的考虑提高测试效率
2. **内建自测试**：在硬件内部集成测试能力
3. **边界扫描**：标准化的测试接口和方法
4. **故障模型**：从物理缺陷到逻辑抽象的建模
5. **自动测试生成**：算法化的测试向量生成

硬件测试的独特挑战：
- 物理缺陷的多样性
- 制造规模和成本压力
- 实时性能要求
- 永久性故障的严重性

与软件测试的对比：
- 更强调物理层面的故障
- 更注重测试的经济性
- 更依赖专用的测试设备
- 更严格的正确性要求

技术发展趋势：
- 人工智能在测试优化中的应用
- 新兴工艺带来的测试挑战
- 在线测试和自修复技术
- 安全测试的重要性提升

下一章，我们将探讨机器学习系统测试，看看这些传统的测试理念如何适应AI时代的新挑战。