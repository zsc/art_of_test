# 第7章：GUI和浏览器测试

图形用户界面（GUI）测试是软件测试中最直观但也最具挑战性的领域之一。本章深入探讨现代Web应用的GUI测试技术，从DOM操作到视觉验证，从可访问性到移动适配，全面覆盖GUI测试的各个方面。

## 7.1 DOM操作和验证

文档对象模型（DOM）是Web页面的编程接口，理解和有效操作DOM是GUI测试的基础。本节探讨DOM测试的核心概念和技术。

### 7.1.1 DOM结构理解

DOM将HTML/XML文档表示为树形结构，每个节点代表文档的一部分：

**节点类型**：
1. **元素节点**：HTML标签（如`<div>`, `<p>`）
2. **文本节点**：元素中的文本内容
3. **属性节点**：元素的属性
4. **注释节点**：HTML注释
5. **文档节点**：整个文档的根

**DOM树示例**：
```html
<html>
  <body>
    <div id="container" class="main">
      <h1>标题</h1>
      <p>段落<span>文本</span></p>
    </div>
  </body>
</html>
```

对应的DOM树：
```
Document
└── html
    └── body
        └── div#container.main
            ├── h1
            │   └── "标题" (文本节点)
            └── p
                ├── "段落" (文本节点)
                └── span
                    └── "文本" (文本节点)
```

### 7.1.2 元素定位策略

有效的元素定位是GUI测试的关键。不同的定位策略有不同的优缺点：

**1. ID定位**
```javascript
// 最快最可靠（如果ID唯一且稳定）
document.getElementById('submit-button')
driver.find_element(By.ID, 'submit-button')
```

**2. CSS选择器**
```javascript
// 灵活强大
document.querySelector('.form-container > button[type="submit"]')
document.querySelectorAll('.product-card:nth-child(odd)')
```

**3. XPath**
```javascript
// 功能最全面，但性能较差
document.evaluate('//div[@class="container"]//button[contains(text(), "提交")]', document)
```

**4. 相对定位（Selenium 4+）**
```python
# 基于其他元素的相对位置
from selenium.webdriver.support.relative_locator import locate_with
password_field = driver.find_element(By.ID, "password")
username_field = driver.find_element(locate_with(By.TAG_NAME, "input").above(password_field))
```

### 7.1.3 定位器稳定性设计

**最佳实践层次**（从最稳定到最不稳定）：
1. **专用测试属性**：`data-testid`, `data-test`
2. **语义化HTML**：`<button>`, `<nav>`, `<main>`
3. **ARIA属性**：`role`, `aria-label`
4. **稳定的类名**：功能性类名而非样式类名
5. **文本内容**：用于不会国际化的内容
6. **元素关系**：父子、兄弟关系
7. **索引位置**：避免使用，除非没有其他选择

### 7.1.4 DOM状态验证

**1. 元素存在性**
```python
def wait_for_element_present(locator, timeout=10):
    """等待元素出现在DOM中"""
    return WebDriverWait(driver, timeout).until(
        EC.presence_of_element_located(locator)
    )

def verify_element_not_present(locator):
    """验证元素不在DOM中"""
    try:
        driver.find_element(*locator)
        return False
    except NoSuchElementException:
        return True
```

**2. 元素可见性**
```python
def is_element_visible(element):
    """检查元素是否可见"""
    # 元素必须存在
    if not element:
        return False
    
    # 检查display属性
    if element.value_of_css_property('display') == 'none':
        return False
    
    # 检查visibility
    if element.value_of_css_property('visibility') == 'hidden':
        return False
    
    # 检查opacity
    if float(element.value_of_css_property('opacity')) == 0:
        return False
    
    # 检查尺寸
    rect = element.rect
    if rect['width'] == 0 or rect['height'] == 0:
        return False
    
    return True
```

**3. 元素状态**
```python
class ElementStateValidator:
    """元素状态验证器"""
    
    def is_enabled(self, element):
        """检查元素是否启用"""
        return element.is_enabled() and not element.get_attribute('disabled')
    
    def is_selected(self, element):
        """检查元素是否被选中（复选框、单选按钮）"""
        return element.is_selected()
    
    def has_focus(self, element):
        """检查元素是否有焦点"""
        return element == driver.switch_to.active_element
    
    def get_validation_state(self, element):
        """获取表单验证状态"""
        return {
            'valid': driver.execute_script('return arguments[0].validity.valid', element),
            'error_message': element.get_attribute('validationMessage')
        }
```

### 7.1.5 DOM变化监测

**1. MutationObserver集成**
```javascript
// 注入DOM变化监测脚本
const observerScript = `
window.domChanges = [];
const observer = new MutationObserver((mutations) => {
    mutations.forEach((mutation) => {
        window.domChanges.push({
            type: mutation.type,
            target: mutation.target.tagName,
            timestamp: Date.now()
        });
    });
});

observer.observe(document.body, {
    childList: true,
    attributes: true,
    subtree: true,
    attributeOldValue: true
});
`;

driver.execute_script(observerScript);
```

**2. Shadow DOM处理**
```python
def find_in_shadow_dom(host_element, selector):
    """在Shadow DOM中查找元素"""
    shadow_root = driver.execute_script(
        'return arguments[0].shadowRoot', 
        host_element
    )
    return shadow_root.find_element(By.CSS_SELECTOR, selector)

# 递归搜索Shadow DOM
def deep_shadow_search(selector):
    script = """
    function findInShadow(selector, root = document) {
        let element = root.querySelector(selector);
        if (element) return element;
        
        const shadows = root.querySelectorAll('*');
        for (let el of shadows) {
            if (el.shadowRoot) {
                element = findInShadow(selector, el.shadowRoot);
                if (element) return element;
            }
        }
        return null;
    }
    return findInShadow(arguments[0]);
    """
    return driver.execute_script(script, selector)
```

### 7.1.6 性能考虑

**1. 批量DOM操作**
```python
def batch_dom_verification(elements_config):
    """批量验证DOM元素，减少往返次数"""
    script = """
    const results = {};
    const configs = arguments[0];
    
    configs.forEach(config => {
        const element = document.querySelector(config.selector);
        results[config.name] = {
            exists: !!element,
            visible: element ? element.offsetParent !== null : false,
            text: element ? element.textContent : null,
            attributes: element ? Object.fromEntries(
                Array.from(element.attributes).map(attr => [attr.name, attr.value])
            ) : {}
        };
    });
    
    return results;
    """
    return driver.execute_script(script, elements_config)
```

**2. 虚拟DOM对比**
```python
class VirtualDOMComparator:
    """虚拟DOM对比，用于验证大型DOM变化"""
    
    def capture_dom_snapshot(self):
        """捕获DOM快照"""
        script = """
        function serializeDOM(node) {
            if (node.nodeType === Node.TEXT_NODE) {
                return node.textContent;
            }
            
            const obj = {
                tag: node.tagName,
                attributes: {},
                children: []
            };
            
            // 收集属性
            for (let attr of node.attributes) {
                obj.attributes[attr.name] = attr.value;
            }
            
            // 递归处理子节点
            for (let child of node.childNodes) {
                if (child.nodeType === Node.ELEMENT_NODE || 
                    (child.nodeType === Node.TEXT_NODE && child.textContent.trim())) {
                    obj.children.push(serializeDOM(child));
                }
            }
            
            return obj;
        }
        
        return serializeDOM(document.body);
        """
        return driver.execute_script(script)
    
    def compare_snapshots(self, before, after):
        """比较两个DOM快照"""
        differences = []
        self._compare_nodes(before, after, '/', differences)
        return differences
```

### 练习 7.1

1. 设计一个健壮的元素定位策略，处理动态生成的表格数据。

<details>
<summary>参考答案</summary>

动态表格的健壮定位策略：

```python
class DynamicTableHandler:
    """处理动态表格的定位和验证"""
    
    def __init__(self, driver):
        self.driver = driver
        
    def locate_cell_by_content(self, row_identifier, column_header, timeout=10):
        """通过行标识和列标题定位单元格"""
        # 先找到列索引
        column_index = self._get_column_index(column_header)
        
        # 再找到目标行
        row = self._find_row_by_identifier(row_identifier)
        
        # 定位具体单元格
        cell_xpath = f".//td[{column_index}]"
        return row.find_element(By.XPATH, cell_xpath)
    
    def _get_column_index(self, header_text):
        """获取列索引（1-based）"""
        headers = self.driver.find_elements(By.CSS_SELECTOR, "table thead th")
        for index, header in enumerate(headers, 1):
            if header.text.strip() == header_text:
                return index
        raise ValueError(f"Column '{header_text}' not found")
    
    def _find_row_by_identifier(self, identifier):
        """通过唯一标识找到行"""
        # 策略1：data属性
        row = self._try_find_element(
            f"table tbody tr[data-row-id='{identifier}']"
        )
        if row:
            return row
        
        # 策略2：第一列内容
        rows = self.driver.find_elements(By.CSS_SELECTOR, "table tbody tr")
        for row in rows:
            first_cell = row.find_element(By.CSS_SELECTOR, "td:first-child")
            if first_cell.text.strip() == str(identifier):
                return row
        
        # 策略3：任意单元格包含标识
        xpath = f"//table/tbody/tr[.//td[contains(text(), '{identifier}')]]"
        return self.driver.find_element(By.XPATH, xpath)
    
    def wait_for_table_stable(self, timeout=10):
        """等待表格数据加载完成并稳定"""
        def table_is_stable(driver):
            # 检查加载指示器消失
            loading_indicators = driver.find_elements(
                By.CSS_SELECTOR, ".table-loading, .spinner"
            )
            if any(indicator.is_displayed() for indicator in loading_indicators):
                return False
            
            # 检查表格存在且有数据
            rows = driver.find_elements(By.CSS_SELECTOR, "table tbody tr")
            if len(rows) == 0:
                return False
            
            # 检查没有"加载中"的占位文本
            table_text = driver.find_element(By.CSS_SELECTOR, "table").text
            if "loading" in table_text.lower() or "加载中" in table_text:
                return False
            
            return True
        
        WebDriverWait(self.driver, timeout).until(table_is_stable)
    
    def get_table_data_as_dict(self):
        """将表格数据转换为字典列表"""
        self.wait_for_table_stable()
        
        # 获取表头
        headers = [
            th.text.strip() 
            for th in self.driver.find_elements(By.CSS_SELECTOR, "table thead th")
        ]
        
        # 获取所有行数据
        rows = self.driver.find_elements(By.CSS_SELECTOR, "table tbody tr")
        data = []
        
        for row in rows:
            cells = row.find_elements(By.TAG_NAME, "td")
            row_data = {}
            for header, cell in zip(headers, cells):
                row_data[header] = cell.text.strip()
            data.append(row_data)
        
        return data
    
    def verify_sorted_by_column(self, column_header, ascending=True):
        """验证表格按指定列排序"""
        data = self.get_table_data_as_dict()
        column_values = [row[column_header] for row in data]
        
        # 尝试数字排序
        try:
            numeric_values = [float(v.replace(',', '')) for v in column_values]
            expected = sorted(numeric_values, reverse=not ascending)
            return numeric_values == expected
        except ValueError:
            # 字符串排序
            expected = sorted(column_values, reverse=not ascending)
            return column_values == expected

# 使用示例
table_handler = DynamicTableHandler(driver)
table_handler.wait_for_table_stable()

# 定位特定单元格
price_cell = table_handler.locate_cell_by_content(
    row_identifier="PROD-123",  # 产品ID
    column_header="价格"
)

# 验证排序
assert table_handler.verify_sorted_by_column("价格", ascending=False)
```
</details>

2. 如何测试一个复杂的单页应用（SPA）的路由变化而不刷新页面？

<details>
<summary>参考答案</summary>

SPA路由测试策略：

```python
class SPARouteHandler:
    """单页应用路由测试处理器"""
    
    def __init__(self, driver):
        self.driver = driver
        self.initial_page_id = self._get_page_id()
    
    def _get_page_id(self):
        """获取页面唯一标识（用于检测真正的页面刷新）"""
        return self.driver.execute_script(
            "return window.performance.navigation.type"
        )
    
    def setup_route_observer(self):
        """设置路由变化观察器"""
        script = """
        window.routeChanges = [];
        
        // 监听 History API
        const originalPushState = history.pushState;
        const originalReplaceState = history.replaceState;
        
        history.pushState = function() {
            originalPushState.apply(history, arguments);
            window.routeChanges.push({
                type: 'pushState',
                url: arguments[2],
                timestamp: Date.now()
            });
        };
        
        history.replaceState = function() {
            originalReplaceState.apply(history, arguments);
            window.routeChanges.push({
                type: 'replaceState',
                url: arguments[2],
                timestamp: Date.now()
            });
        };
        
        // 监听 popstate 事件（浏览器前进/后退）
        window.addEventListener('popstate', function(event) {
            window.routeChanges.push({
                type: 'popstate',
                url: location.pathname,
                timestamp: Date.now()
            });
        });
        
        // 监听 hashchange 事件
        window.addEventListener('hashchange', function(event) {
            window.routeChanges.push({
                type: 'hashchange',
                url: location.hash,
                timestamp: Date.now()
            });
        });
        """
        self.driver.execute_script(script)
    
    def wait_for_route_change(self, expected_route=None, timeout=10):
        """等待路由变化"""
        start_time = time.time()
        initial_url = self.driver.current_url
        
        while time.time() - start_time < timeout:
            current_url = self.driver.current_url
            
            # 检查URL变化
            if current_url != initial_url:
                if expected_route is None or expected_route in current_url:
                    return True
            
            # 检查记录的路由变化
            route_changes = self.driver.execute_script(
                "return window.routeChanges || []"
            )
            if route_changes:
                latest_change = route_changes[-1]
                if expected_route is None or expected_route in latest_change['url']:
                    return True
            
            time.sleep(0.1)
        
        return False
    
    def verify_no_page_reload(self):
        """验证页面没有真正刷新"""
        current_page_id = self._get_page_id()
        return current_page_id == self.initial_page_id
    
    def test_spa_navigation(self):
        """完整的SPA导航测试示例"""
        # 设置观察器
        self.setup_route_observer()
        
        # 测试路由导航
        test_routes = [
            ('/home', 'home-container'),
            ('/products', 'product-list'),
            ('/about', 'about-section'),
            ('/contact', 'contact-form')
        ]
        
        for route, expected_element_id in test_routes:
            # 点击导航链接
            nav_link = self.driver.find_element(
                By.CSS_SELECTOR, f'a[href="{route}"]'
            )
            nav_link.click()
            
            # 等待路由变化
            assert self.wait_for_route_change(route), \
                f"Route change to {route} failed"
            
            # 验证没有页面刷新
            assert self.verify_no_page_reload(), \
                "Unexpected page reload detected"
            
            # 验证内容加载
            WebDriverWait(self.driver, 10).until(
                EC.presence_of_element_located((By.ID, expected_element_id))
            )
            
            # 验证URL更新
            assert route in self.driver.current_url, \
                f"URL not updated to include {route}"
    
    def test_browser_navigation(self):
        """测试浏览器前进/后退按钮"""
        # 导航到多个页面建立历史
        self.driver.find_element(By.LINK_TEXT, "Products").click()
        self.wait_for_route_change('/products')
        
        self.driver.find_element(By.LINK_TEXT, "About").click()
        self.wait_for_route_change('/about')
        
        # 测试后退
        self.driver.back()
        assert self.wait_for_route_change('/products'), \
            "Back navigation failed"
        
        # 测试前进
        self.driver.forward()
        assert self.wait_for_route_change('/about'), \
            "Forward navigation failed"
        
        # 验证整个过程没有页面刷新
        assert self.verify_no_page_reload()
    
    def test_deep_linking(self):
        """测试直接访问深层链接"""
        deep_link = self.driver.current_url.split('#')[0] + '#/products/123'
        
        # 直接导航到深层链接
        self.driver.get(deep_link)
        
        # 等待内容加载
        WebDriverWait(self.driver, 10).until(
            EC.presence_of_element_located((By.CLASS_NAME, "product-detail"))
        )
        
        # 验证路由正确解析
        assert '/products/123' in self.driver.current_url
        
    def get_route_performance_metrics(self):
        """获取路由切换性能指标"""
        script = """
        const changes = window.routeChanges || [];
        const metrics = [];
        
        for (let i = 1; i < changes.length; i++) {
            const duration = changes[i].timestamp - changes[i-1].timestamp;
            metrics.push({
                from: changes[i-1].url,
                to: changes[i].url,
                duration: duration,
                type: changes[i].type
            });
        }
        
        return metrics;
        """
        return self.driver.execute_script(script)

# 使用示例
spa_handler = SPARouteHandler(driver)
spa_handler.test_spa_navigation()
spa_handler.test_browser_navigation()

# 性能分析
metrics = spa_handler.get_route_performance_metrics()
for metric in metrics:
    print(f"Route change from {metric['from']} to {metric['to']}: {metric['duration']}ms")
```

这个解决方案提供了：
1. 路由变化的自动检测
2. 页面刷新的验证
3. 浏览器导航支持
4. 深层链接测试
5. 性能指标收集
</details>

### 进一步研究

- DOM差异算法：如何高效比较两个DOM树的差异？
- Web Components测试：如何测试自定义元素和Shadow DOM？
- 虚拟滚动测试：如何测试只渲染可见部分的大型列表？
- DOM性能分析：如何检测和预防DOM操作导致的性能问题？
- 跨框架DOM测试：如何编写适用于React、Vue、Angular的通用DOM测试？

## 7.2 视觉回归测试

视觉回归测试通过比较UI的视觉外观来检测意外的变化。与传统的功能测试不同，视觉测试关注的是"看起来对不对"而不是"工作正不正常"。

### 7.2.1 视觉测试的必要性

传统DOM测试的局限性：
- 无法检测CSS变化导致的视觉问题
- 忽略布局错位、重叠等问题  
- 无法验证字体、颜色、间距等视觉属性
- 难以测试复杂的视觉交互效果

视觉测试填补了这些空白，确保用户看到的界面符合预期。

### 7.2.2 视觉测试基础技术

**1. 像素级对比**
```python
class PixelComparator:
    """像素级图像对比"""
    
    def compare_images(self, baseline, current, threshold=0.1):
        """比较两张图片的像素差异"""
        # 确保图片尺寸相同
        if baseline.size != current.size:
            return False, "图片尺寸不匹配"
        
        # 逐像素比较
        diff_pixels = 0
        total_pixels = baseline.width * baseline.height
        
        for x in range(baseline.width):
            for y in range(baseline.height):
                pixel1 = baseline.getpixel((x, y))
                pixel2 = current.getpixel((x, y))
                
                if not self._pixels_match(pixel1, pixel2):
                    diff_pixels += 1
        
        diff_percentage = diff_pixels / total_pixels
        return diff_percentage <= threshold, diff_percentage
    
    def _pixels_match(self, pixel1, pixel2, tolerance=5):
        """判断两个像素是否匹配（允许一定容差）"""
        for i in range(3):  # RGB
            if abs(pixel1[i] - pixel2[i]) > tolerance:
                return False
        return True
```

**2. 结构相似性（SSIM）**
```python
from skimage.metrics import structural_similarity as ssim
import cv2

class StructuralComparator:
    """基于结构相似性的比较"""
    
    def compare_structure(self, baseline_path, current_path):
        """使用SSIM算法比较图像结构"""
        # 读取图像
        baseline = cv2.imread(baseline_path)
        current = cv2.imread(current_path)
        
        # 转换为灰度图
        baseline_gray = cv2.cvtColor(baseline, cv2.COLOR_BGR2GRAY)
        current_gray = cv2.cvtColor(current, cv2.COLOR_BGR2GRAY)
        
        # 计算SSIM
        score, diff = ssim(baseline_gray, current_gray, full=True)
        
        # 生成差异图
        diff = (diff * 255).astype("uint8")
        
        return {
            'score': score,  # 1.0表示完全相同
            'passed': score > 0.95,
            'diff_image': diff
        }
```

**3. 感知哈希**
```python
import imagehash

class PerceptualHashComparator:
    """感知哈希比较，对细微变化不敏感"""
    
    def compare_perceptual(self, image1_path, image2_path):
        """使用感知哈希比较图像"""
        hash1 = imagehash.average_hash(Image.open(image1_path))
        hash2 = imagehash.average_hash(Image.open(image2_path))
        
        # 计算汉明距离
        distance = hash1 - hash2
        
        return {
            'similar': distance < 5,  # 阈值可调
            'distance': distance,
            'hash1': str(hash1),
            'hash2': str(hash2)
        }
```

### 7.2.3 智能视觉对比策略

**1. 忽略动态内容**
```python
class SmartVisualComparator:
    """智能视觉比较，处理动态内容"""
    
    def __init__(self):
        self.ignore_regions = []
        self.dynamic_selectors = []
    
    def add_ignore_region(self, x, y, width, height):
        """添加忽略区域（如时间戳、广告）"""
        self.ignore_regions.append({
            'x': x, 'y': y, 
            'width': width, 'height': height
        })
    
    def add_dynamic_selector(self, selector):
        """添加动态内容选择器"""
        self.dynamic_selectors.append(selector)
    
    def mask_dynamic_content(self, driver, screenshot):
        """遮盖动态内容"""
        for selector in self.dynamic_selectors:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
            for element in elements:
                if element.is_displayed():
                    # 获取元素位置和大小
                    rect = element.rect
                    # 在截图上遮盖该区域
                    self._mask_region(screenshot, rect)
        
        return screenshot
    
    def _mask_region(self, image, rect):
        """用纯色遮盖指定区域"""
        draw = ImageDraw.Draw(image)
        draw.rectangle([
            rect['x'], rect['y'],
            rect['x'] + rect['width'],
            rect['y'] + rect['height']
        ], fill='black')
```

**2. 响应式布局测试**
```python
class ResponsiveVisualTester:
    """响应式设计的视觉测试"""
    
    def __init__(self, driver):
        self.driver = driver
        self.breakpoints = {
            'mobile': (375, 667),
            'tablet': (768, 1024),
            'desktop': (1920, 1080)
        }
    
    def test_all_breakpoints(self, url, baseline_dir):
        """测试所有断点的视觉效果"""
        results = {}
        
        for device, (width, height) in self.breakpoints.items():
            # 设置视口大小
            self.driver.set_window_size(width, height)
            self.driver.get(url)
            
            # 等待页面稳定
            self._wait_for_stable_layout()
            
            # 截图
            screenshot_path = f'current_{device}.png'
            self.driver.save_screenshot(screenshot_path)
            
            # 比较
            baseline_path = f'{baseline_dir}/{device}.png'
            if os.path.exists(baseline_path):
                results[device] = self._compare_screenshots(
                    baseline_path, screenshot_path
                )
            else:
                # 首次运行，保存为基准
                shutil.copy(screenshot_path, baseline_path)
                results[device] = {'status': 'baseline_created'}
        
        return results
    
    def _wait_for_stable_layout(self):
        """等待布局稳定（响应式调整完成）"""
        script = """
        return new Promise((resolve) => {
            let lastHeight = document.body.scrollHeight;
            let checks = 0;
            
            const checkStability = () => {
                const currentHeight = document.body.scrollHeight;
                if (currentHeight === lastHeight) {
                    checks++;
                    if (checks >= 3) {
                        resolve(true);
                        return;
                    }
                } else {
                    checks = 0;
                    lastHeight = currentHeight;
                }
                setTimeout(checkStability, 100);
            };
            
            checkStability();
        });
        """
        self.driver.execute_async_script(script)
```

### 7.2.4 视觉测试工作流

**1. 基准管理**
```python
class BaselineManager:
    """视觉测试基准管理"""
    
    def __init__(self, base_dir='visual_baselines'):
        self.base_dir = base_dir
        self.metadata_file = os.path.join(base_dir, 'metadata.json')
        self._ensure_directory()
    
    def save_baseline(self, test_name, image, metadata=None):
        """保存基准图像"""
        timestamp = datetime.now().isoformat()
        filename = f"{test_name}_{timestamp}.png"
        filepath = os.path.join(self.base_dir, filename)
        
        # 保存图像
        image.save(filepath)
        
        # 更新元数据
        self._update_metadata(test_name, filename, metadata)
        
        return filepath
    
    def get_baseline(self, test_name):
        """获取最新的基准图像"""
        metadata = self._load_metadata()
        if test_name in metadata:
            filename = metadata[test_name]['current']
            return os.path.join(self.base_dir, filename)
        return None
    
    def approve_change(self, test_name, new_image_path):
        """批准视觉变更，更新基准"""
        # 归档旧基准
        old_baseline = self.get_baseline(test_name)
        if old_baseline:
            self._archive_baseline(test_name, old_baseline)
        
        # 设置新基准
        new_baseline = self.save_baseline(test_name, Image.open(new_image_path))
        return new_baseline
    
    def _archive_baseline(self, test_name, old_path):
        """归档旧的基准图像"""
        archive_dir = os.path.join(self.base_dir, 'archive', test_name)
        os.makedirs(archive_dir, exist_ok=True)
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        archive_name = f"baseline_{timestamp}.png"
        shutil.move(old_path, os.path.join(archive_dir, archive_name))
```

**2. 差异报告生成**
```python
class VisualDiffReporter:
    """视觉差异报告生成器"""
    
    def generate_diff_image(self, baseline, current, diff_path):
        """生成差异对比图"""
        # 创建三栏对比图
        width = baseline.width
        height = baseline.height
        
        # 创建新图像（3倍宽度）
        diff_image = Image.new('RGB', (width * 3, height))
        
        # 粘贴基准图像
        diff_image.paste(baseline, (0, 0))
        
        # 粘贴当前图像
        diff_image.paste(current, (width, 0))
        
        # 生成差异高亮
        diff_highlight = self._create_diff_highlight(baseline, current)
        diff_image.paste(diff_highlight, (width * 2, 0))
        
        # 添加标签
        self._add_labels(diff_image, ['Baseline', 'Current', 'Diff'])
        
        diff_image.save(diff_path)
        return diff_path
    
    def _create_diff_highlight(self, img1, img2):
        """创建差异高亮图"""
        diff = Image.new('RGB', img1.size)
        pixels1 = img1.load()
        pixels2 = img2.load()
        pixels_diff = diff.load()
        
        for x in range(img1.width):
            for y in range(img1.height):
                if pixels1[x, y] != pixels2[x, y]:
                    # 差异部分标记为红色
                    pixels_diff[x, y] = (255, 0, 0)
                else:
                    # 相同部分保持原样（灰度）
                    gray = int(sum(pixels1[x, y]) / 3)
                    pixels_diff[x, y] = (gray, gray, gray)
        
        return diff
    
    def generate_html_report(self, test_results, output_path):
        """生成HTML格式的视觉测试报告"""
        html_template = """
        <html>
        <head>
            <title>视觉回归测试报告</title>
            <style>
                .test-result { margin: 20px 0; border: 1px solid #ddd; }
                .failed { background-color: #fee; }
                .passed { background-color: #efe; }
                .diff-container { display: flex; gap: 10px; }
                .diff-image { max-width: 100%; }
            </style>
        </head>
        <body>
            <h1>视觉回归测试报告</h1>
            <p>生成时间: {timestamp}</p>
            <p>通过: {passed}/{total}</p>
            
            {test_sections}
        </body>
        </html>
        """
        
        # 生成测试结果部分
        sections = []
        for test_name, result in test_results.items():
            status_class = 'passed' if result['passed'] else 'failed'
            section = f"""
            <div class="test-result {status_class}">
                <h2>{test_name}</h2>
                <p>状态: {'通过' if result['passed'] else '失败'}</p>
                <p>相似度: {result.get('similarity', 'N/A')}%</p>
                {self._generate_image_section(result)}
            </div>
            """
            sections.append(section)
        
        # 填充模板
        html_content = html_template.format(
            timestamp=datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            passed=sum(1 for r in test_results.values() if r['passed']),
            total=len(test_results),
            test_sections='\n'.join(sections)
        )
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
```

### 7.2.5 高级视觉测试技术

**1. AI驱动的视觉验证**
```python
class AIVisualValidator:
    """使用AI模型进行视觉验证"""
    
    def __init__(self, model_path):
        self.model = self._load_model(model_path)
    
    def validate_layout(self, screenshot):
        """验证布局是否合理"""
        # 检测UI元素
        elements = self._detect_ui_elements(screenshot)
        
        # 验证对齐
        alignment_issues = self._check_alignment(elements)
        
        # 验证间距
        spacing_issues = self._check_spacing(elements)
        
        # 验证重叠
        overlap_issues = self._check_overlaps(elements)
        
        return {
            'valid': len(alignment_issues) == 0 and 
                    len(spacing_issues) == 0 and 
                    len(overlap_issues) == 0,
            'issues': {
                'alignment': alignment_issues,
                'spacing': spacing_issues,
                'overlap': overlap_issues
            }
        }
    
    def detect_visual_anomalies(self, screenshot, baseline_stats):
        """检测视觉异常"""
        current_stats = self._extract_visual_features(screenshot)
        
        anomalies = []
        
        # 颜色分布异常
        if self._color_distribution_changed(
            baseline_stats['colors'], 
            current_stats['colors']
        ):
            anomalies.append('颜色分布显著变化')
        
        # 文本密度异常
        if abs(baseline_stats['text_density'] - 
               current_stats['text_density']) > 0.2:
            anomalies.append('文本密度异常')
        
        # 复杂度异常
        if abs(baseline_stats['complexity'] - 
               current_stats['complexity']) > 0.3:
            anomalies.append('视觉复杂度异常')
        
        return anomalies
```

**2. 跨浏览器视觉一致性**
```python
class CrossBrowserVisualTester:
    """跨浏览器视觉一致性测试"""
    
    def __init__(self, browsers):
        self.browsers = browsers  # [(driver, name), ...]
    
    def test_visual_consistency(self, url, test_name):
        """测试跨浏览器的视觉一致性"""
        screenshots = {}
        
        # 收集所有浏览器的截图
        for driver, browser_name in self.browsers:
            driver.get(url)
            self._wait_for_page_ready(driver)
            
            screenshot_path = f"{test_name}_{browser_name}.png"
            driver.save_screenshot(screenshot_path)
            screenshots[browser_name] = screenshot_path
        
        # 交叉比较
        results = {}
        browser_names = list(screenshots.keys())
        
        for i in range(len(browser_names)):
            for j in range(i + 1, len(browser_names)):
                browser1, browser2 = browser_names[i], browser_names[j]
                comparison_key = f"{browser1}_vs_{browser2}"
                
                results[comparison_key] = self._compare_browsers(
                    screenshots[browser1],
                    screenshots[browser2]
                )
        
        return results
    
    def _normalize_screenshot(self, screenshot_path):
        """标准化截图（处理浏览器差异）"""
        img = Image.open(screenshot_path)
        
        # 处理抗锯齿差异
        img = img.filter(ImageFilter.SMOOTH_MORE)
        
        # 处理字体渲染差异（轻微模糊）
        img = img.filter(ImageFilter.GaussianBlur(radius=0.5))
        
        return img
```

### 7.2.6 视觉测试最佳实践

**1. 稳定性保证**
```python
def ensure_visual_stability(driver):
    """确保页面视觉稳定后再截图"""
    # 等待动画完成
    driver.execute_script("""
        // 禁用CSS动画
        const style = document.createElement('style');
        style.textContent = '* { animation-duration: 0s !important; }';
        document.head.appendChild(style);
    """)
    
    # 等待字体加载
    driver.execute_script("""
        return document.fonts.ready;
    """)
    
    # 等待图片加载
    driver.execute_script("""
        return Promise.all(
            Array.from(document.images)
                .filter(img => !img.complete)
                .map(img => new Promise(resolve => {
                    img.addEventListener('load', resolve);
                    img.addEventListener('error', resolve);
                }))
        );
    """)
    
    # 滚动到顶部确保一致性
    driver.execute_script("window.scrollTo(0, 0);")
    
    # 固定时间等待（处理渐进式渲染）
    time.sleep(1)
```

**2. 性能优化**
```python
class OptimizedVisualTester:
    """优化的视觉测试器"""
    
    def __init__(self):
        self.screenshot_cache = {}
        self.comparison_cache = {}
    
    def smart_screenshot(self, driver, element=None):
        """智能截图（只截取变化的部分）"""
        if element:
            # 元素截图
            return element.screenshot_as_png
        else:
            # 全页面截图优化
            viewport_height = driver.execute_script(
                "return window.innerHeight"
            )
            total_height = driver.execute_script(
                "return document.body.scrollHeight"
            )
            
            if total_height <= viewport_height:
                # 单屏截图
                return driver.get_screenshot_as_png()
            else:
                # 长页面分段截图
                return self._capture_full_page(driver)
    
    def incremental_comparison(self, baseline, current, regions):
        """增量比较（只比较指定区域）"""
        differences = []
        
        for region in regions:
            baseline_crop = self._crop_region(baseline, region)
            current_crop = self._crop_region(current, region)
            
            if not self._images_match(baseline_crop, current_crop):
                differences.append(region)
        
        return differences
```

### 练习 7.2

1. 设计一个视觉测试策略来验证暗黑模式切换的正确性。

<details>
<summary>参考答案</summary>

暗黑模式视觉测试策略：

```python
class DarkModeVisualTester:
    """暗黑模式视觉测试"""
    
    def __init__(self, driver):
        self.driver = driver
        self.color_validator = ColorValidator()
    
    def test_dark_mode_switch(self, url):
        """测试暗黑模式切换"""
        results = {
            'color_contrast': {},
            'element_visibility': {},
            'theme_consistency': {},
            'transition_smoothness': {}
        }
        
        # 1. 测试亮色模式
        self.driver.get(url)
        light_mode_data = self._capture_theme_data('light')
        
        # 2. 切换到暗黑模式
        self._switch_theme('dark')
        dark_mode_data = self._capture_theme_data('dark')
        
        # 3. 验证颜色对比度
        results['color_contrast'] = self._verify_contrast_ratios(dark_mode_data)
        
        # 4. 验证元素可见性
        results['element_visibility'] = self._verify_visibility(
            light_mode_data, dark_mode_data
        )
        
        # 5. 验证主题一致性
        results['theme_consistency'] = self._verify_theme_consistency(dark_mode_data)
        
        # 6. 验证过渡效果
        results['transition_smoothness'] = self._test_transition_animation()
        
        return results
    
    def _capture_theme_data(self, theme_name):
        """捕获主题数据"""
        # 等待主题应用完成
        time.sleep(0.5)
        
        # 截图
        screenshot = self.driver.get_screenshot_as_png()
        
        # 提取颜色信息
        colors = self._extract_color_palette(screenshot)
        
        # 提取计算样式
        computed_styles = self._extract_computed_styles()
        
        return {
            'screenshot': screenshot,
            'colors': colors,
            'styles': computed_styles,
            'theme': theme_name
        }
    
    def _extract_computed_styles(self):
        """提取关键元素的计算样式"""
        script = """
        const elements = {
            body: document.body,
            header: document.querySelector('header'),
            main: document.querySelector('main'),
            buttons: Array.from(document.querySelectorAll('button')),
            inputs: Array.from(document.querySelectorAll('input')),
            cards: Array.from(document.querySelectorAll('.card'))
        };
        
        const styles = {};
        
        for (const [key, element] of Object.entries(elements)) {
            if (element instanceof Array) {
                styles[key] = element.map(el => {
                    const computed = window.getComputedStyle(el);
                    return {
                        backgroundColor: computed.backgroundColor,
                        color: computed.color,
                        borderColor: computed.borderColor
                    };
                });
            } else if (element) {
                const computed = window.getComputedStyle(element);
                styles[key] = {
                    backgroundColor: computed.backgroundColor,
                    color: computed.color,
                    borderColor: computed.borderColor
                };
            }
        }
        
        return styles;
        """
        return self.driver.execute_script(script)
    
    def _verify_contrast_ratios(self, dark_mode_data):
        """验证暗黑模式下的对比度"""
        issues = []
        styles = dark_mode_data['styles']
        
        # WCAG AA标准：普通文本4.5:1，大文本3:1
        min_contrast_normal = 4.5
        min_contrast_large = 3.0
        
        for element, style in styles.items():
            if isinstance(style, list):
                for idx, s in enumerate(style):
                    contrast = self.color_validator.calculate_contrast(
                        s['backgroundColor'], s['color']
                    )
                    if contrast < min_contrast_normal:
                        issues.append({
                            'element': f"{element}[{idx}]",
                            'contrast': contrast,
                            'required': min_contrast_normal
                        })
            else:
                contrast = self.color_validator.calculate_contrast(
                    style['backgroundColor'], style['color']
                )
                if contrast < min_contrast_normal:
                    issues.append({
                        'element': element,
                        'contrast': contrast,
                        'required': min_contrast_normal
                    })
        
        return {
            'passed': len(issues) == 0,
            'issues': issues
        }
    
    def _verify_theme_consistency(self, dark_mode_data):
        """验证暗黑主题的一致性"""
        colors = dark_mode_data['colors']
        
        # 检查是否真的是暗色主题
        dark_pixels = sum(1 for color in colors if self._is_dark_color(color))
        total_pixels = len(colors)
        dark_ratio = dark_pixels / total_pixels
        
        # 检查颜色和谐性
        color_harmony = self._check_color_harmony(colors)
        
        return {
            'is_dark_theme': dark_ratio > 0.6,
            'dark_ratio': dark_ratio,
            'color_harmony': color_harmony,
            'passed': dark_ratio > 0.6 and color_harmony['score'] > 0.8
        }
    
    def _test_transition_animation(self):
        """测试主题切换动画"""
        # 准备录制
        screenshots = []
        
        # 开始录制切换过程
        self._switch_theme('light')
        time.sleep(0.5)
        
        # 切换并捕获过渡帧
        start_time = time.time()
        self._switch_theme('dark')
        
        while time.time() - start_time < 1.0:  # 录制1秒
            screenshots.append(self.driver.get_screenshot_as_png())
            time.sleep(0.05)  # 20fps
        
        # 分析过渡平滑度
        smoothness_score = self._analyze_transition_smoothness(screenshots)
        
        return {
            'frame_count': len(screenshots),
            'smoothness_score': smoothness_score,
            'passed': smoothness_score > 0.8
        }
    
    def _switch_theme(self, theme):
        """切换主题"""
        script = f"""
        // 尝试多种切换方式
        // 方式1：切换按钮
        const themeToggle = document.querySelector('[data-theme-toggle]');
        if (themeToggle) {{
            themeToggle.click();
            return;
        }}
        
        // 方式2：设置属性
        document.documentElement.setAttribute('data-theme', '{theme}');
        
        // 方式3：切换类名
        document.body.classList.toggle('dark-mode', '{theme}' === 'dark');
        """
        self.driver.execute_script(script)

class ColorValidator:
    """颜色验证工具"""
    
    def calculate_contrast(self, bg_color, fg_color):
        """计算颜色对比度（WCAG标准）"""
        # 转换颜色格式
        bg_rgb = self._parse_color(bg_color)
        fg_rgb = self._parse_color(fg_color)
        
        # 计算相对亮度
        bg_luminance = self._relative_luminance(bg_rgb)
        fg_luminance = self._relative_luminance(fg_rgb)
        
        # 计算对比度
        lighter = max(bg_luminance, fg_luminance)
        darker = min(bg_luminance, fg_luminance)
        
        return (lighter + 0.05) / (darker + 0.05)
    
    def _relative_luminance(self, rgb):
        """计算相对亮度"""
        r, g, b = [self._linearize(val/255) for val in rgb]
        return 0.2126 * r + 0.7152 * g + 0.0722 * b
    
    def _linearize(self, channel):
        """线性化颜色通道"""
        if channel <= 0.03928:
            return channel / 12.92
        return ((channel + 0.055) / 1.055) ** 2.4
```
</details>

2. 如何设计一个视觉测试来验证响应式图片的加载和显示？

<details>
<summary>参考答案</summary>

响应式图片视觉测试设计：

```python
class ResponsiveImageTester:
    """响应式图片测试"""
    
    def __init__(self, driver):
        self.driver = driver
        self.image_analyzer = ImageAnalyzer()
    
    def test_responsive_images(self, url):
        """测试响应式图片在不同条件下的表现"""
        test_scenarios = [
            # (viewport_width, dpr, network, expected_behavior)
            (320, 1, '3g', 'low_quality'),
            (375, 2, '4g', 'retina_mobile'),
            (768, 1, 'wifi', 'tablet_quality'),
            (1920, 1, 'wifi', 'desktop_quality'),
            (3840, 2, 'wifi', 'ultra_hd')
        ]
        
        results = {}
        
        for width, dpr, network, expected in test_scenarios:
            scenario_key = f"{width}px_dpr{dpr}_{network}"
            results[scenario_key] = self._test_scenario(
                url, width, dpr, network, expected
            )
        
        return results
    
    def _test_scenario(self, url, viewport_width, dpr, network, expected_behavior):
        """测试单个场景"""
        # 设置测试条件
        self._setup_test_conditions(viewport_width, dpr, network)
        
        # 加载页面
        self.driver.get(url)
        
        # 等待图片加载
        self._wait_for_images_loaded()
        
        # 收集图片数据
        image_data = self._collect_image_data()
        
        # 验证结果
        validations = {
            'correct_source': self._verify_image_sources(image_data, expected_behavior),
            'visual_quality': self._verify_visual_quality(image_data, expected_behavior),
            'loading_performance': self._verify_loading_performance(image_data),
            'lazy_loading': self._verify_lazy_loading_behavior(),
            'aspect_ratio': self._verify_aspect_ratios(image_data)
        }
        
        return validations
    
    def _setup_test_conditions(self, width, dpr, network):
        """设置测试条件"""
        # 设置视口
        height = int(width * 1.5)  # 假设16:10比例
        self.driver.set_window_size(width, height)
        
        # 设置设备像素比
        self.driver.execute_cdp_cmd('Emulation.setDeviceMetricsOverride', {
            'width': width,
            'height': height,
            'deviceScaleFactor': dpr,
            'mobile': width < 768
        })
        
        # 设置网络条件
        network_conditions = {
            '3g': {
                'offline': False,
                'downloadThroughput': 1.6 * 1024 * 1024 / 8,  # 1.6 Mbps
                'uploadThroughput': 768 * 1024 / 8,  # 768 Kbps
                'latency': 300
            },
            '4g': {
                'offline': False,
                'downloadThroughput': 4 * 1024 * 1024 / 8,  # 4 Mbps
                'uploadThroughput': 3 * 1024 * 1024 / 8,  # 3 Mbps
                'latency': 100
            },
            'wifi': {
                'offline': False,
                'downloadThroughput': 30 * 1024 * 1024 / 8,  # 30 Mbps
                'uploadThroughput': 15 * 1024 * 1024 / 8,  # 15 Mbps
                'latency': 20
            }
        }
        
        self.driver.set_network_conditions(**network_conditions.get(network, {}))
    
    def _collect_image_data(self):
        """收集页面上所有图片的数据"""
        script = """
        return Array.from(document.images).map(img => {
            const rect = img.getBoundingClientRect();
            return {
                src: img.currentSrc || img.src,
                naturalWidth: img.naturalWidth,
                naturalHeight: img.naturalHeight,
                displayWidth: rect.width,
                displayHeight: rect.height,
                loading: img.loading,
                srcset: img.srcset,
                sizes: img.sizes,
                isVisible: rect.top < window.innerHeight && rect.bottom > 0,
                loadTime: performance.getEntriesByName(img.currentSrc || img.src)[0]?.duration || 0,
                fileSize: performance.getEntriesByName(img.currentSrc || img.src)[0]?.transferSize || 0
            };
        });
        """
        return self.driver.execute_script(script)
    
    def _verify_image_sources(self, image_data, expected_behavior):
        """验证图片源选择是否正确"""
        issues = []
        
        for img in image_data:
            # 检查是否使用了正确的图片变体
            if expected_behavior == 'low_quality':
                if 'small' not in img['src'] and img['fileSize'] > 50000:
                    issues.append(f"大文件用于低带宽: {img['src']}")
            
            elif expected_behavior == 'retina_mobile':
                if '@2x' not in img['src'] and 'retina' not in img['src']:
                    issues.append(f"非视网膜图片用于高DPR设备: {img['src']}")
            
            # 检查srcset是否正确实现
            if img['srcset'] and not self._validate_srcset(img['srcset']):
                issues.append(f"无效的srcset: {img['srcset']}")
        
        return {
            'passed': len(issues) == 0,
            'issues': issues
        }
    
    def _verify_visual_quality(self, image_data, expected_behavior):
        """验证视觉质量"""
        quality_scores = []
        
        for img in image_data:
            if not img['isVisible']:
                continue
            
            # 截取图片区域
            element = self.driver.find_element(
                By.CSS_SELECTOR, f'img[src="{img["src"]}"]'
            )
            img_screenshot = element.screenshot_as_png
            
            # 分析图片质量
            quality_analysis = self.image_analyzer.analyze_quality(img_screenshot)
            
            # 根据场景验证质量是否合适
            if expected_behavior == 'low_quality':
                expected_quality = 'acceptable'
            elif 'hd' in expected_behavior:
                expected_quality = 'high'
            else:
                expected_quality = 'good'
            
            quality_scores.append({
                'src': img['src'],
                'quality': quality_analysis['quality'],
                'expected': expected_quality,
                'passed': self._quality_meets_expectation(
                    quality_analysis['quality'], expected_quality
                )
            })
        
        return {
            'passed': all(score['passed'] for score in quality_scores),
            'details': quality_scores
        }
    
    def _verify_lazy_loading_behavior(self):
        """验证懒加载行为"""
        # 初始状态
        initial_loaded = self.driver.execute_script("""
            return Array.from(document.images)
                .filter(img => img.complete && img.naturalHeight > 0)
                .length;
        """)
        
        # 滚动到底部
        self.driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
        time.sleep(1)  # 等待懒加载触发
        
        # 最终状态
        final_loaded = self.driver.execute_script("""
            return Array.from(document.images)
                .filter(img => img.complete && img.naturalHeight > 0)
                .length;
        """)
        
        return {
            'lazy_loading_detected': final_loaded > initial_loaded,
            'initial_loaded': initial_loaded,
            'final_loaded': final_loaded,
            'passed': final_loaded > initial_loaded  # 假设页面应该有懒加载
        }
    
    def _verify_aspect_ratios(self, image_data):
        """验证图片宽高比保持"""
        issues = []
        
        for img in image_data:
            if img['naturalWidth'] == 0 or img['displayWidth'] == 0:
                continue
            
            natural_ratio = img['naturalWidth'] / img['naturalHeight']
            display_ratio = img['displayWidth'] / img['displayHeight']
            
            # 允许1%的误差
            if abs(natural_ratio - display_ratio) / natural_ratio > 0.01:
                issues.append({
                    'src': img['src'],
                    'natural_ratio': natural_ratio,
                    'display_ratio': display_ratio
                })
        
        return {
            'passed': len(issues) == 0,
            'issues': issues
        }

class ImageAnalyzer:
    """图片质量分析器"""
    
    def analyze_quality(self, image_data):
        """分析图片质量"""
        img = Image.open(io.BytesIO(image_data))
        
        # 计算清晰度（使用拉普拉斯算子）
        sharpness = self._calculate_sharpness(img)
        
        # 检测压缩伪影
        compression_artifacts = self._detect_compression_artifacts(img)
        
        # 颜色丰富度
        color_richness = self._analyze_color_richness(img)
        
        # 综合评分
        if sharpness > 100 and compression_artifacts < 0.1:
            quality = 'high'
        elif sharpness > 50 and compression_artifacts < 0.3:
            quality = 'good'
        else:
            quality = 'acceptable'
        
        return {
            'quality': quality,
            'sharpness': sharpness,
            'compression_artifacts': compression_artifacts,
            'color_richness': color_richness
        }
```

这个解决方案测试了：
1. 不同视口和DPR下的图片选择
2. 网络条件对图片加载的影响
3. 视觉质量验证
4. 懒加载行为
5. 宽高比保持
</details>

### 进一步研究

- 基于机器学习的视觉异常检测
- 视觉测试的自动基准更新策略
- 动态内容的视觉测试方法
- 3D和WebGL内容的视觉验证
- 视觉测试在CI/CD中的优化策略

## 7.3 可访问性测试

可访问性（Accessibility, a11y）测试确保所有用户，包括残障人士，都能有效地使用Web应用。这不仅是道德责任和法律要求，也是优秀用户体验的体现。

### 7.3.1 可访问性标准和指南

**WCAG 2.1标准**（Web Content Accessibility Guidelines）定义了四个原则：

1. **可感知（Perceivable）**
   - 信息必须以用户可感知的方式呈现
   - 提供文本替代品
   - 创建可适应不同呈现方式的内容

2. **可操作（Operable）**
   - 界面组件必须可操作
   - 键盘可访问
   - 给用户足够时间

3. **可理解（Understandable）**
   - 信息和UI操作必须可理解
   - 文本可读且可理解
   - 网页以可预测方式运行

4. **健壮（Robust）**
   - 内容必须足够健壮，能被各种用户代理解释
   - 兼容当前和未来的辅助技术

### 7.3.2 自动化可访问性测试

**1. ARIA属性验证**
```python
class ARIAValidator:
    """ARIA属性验证器"""
    
    def validate_aria_attributes(self, driver):
        """验证ARIA属性的正确使用"""
        issues = []
        
        # 验证必需的ARIA标签
        issues.extend(self._check_required_labels(driver))
        
        # 验证ARIA角色
        issues.extend(self._check_aria_roles(driver))
        
        # 验证ARIA状态
        issues.extend(self._check_aria_states(driver))
        
        # 验证ARIA关系
        issues.extend(self._check_aria_relationships(driver))
        
        return issues
    
    def _check_required_labels(self, driver):
        """检查必需的标签"""
        script = """
        const issues = [];
        
        // 检查表单控件
        const formControls = document.querySelectorAll('input, select, textarea');
        formControls.forEach(control => {
            const hasLabel = control.labels && control.labels.length > 0;
            const hasAriaLabel = control.hasAttribute('aria-label');
            const hasAriaLabelledby = control.hasAttribute('aria-labelledby');
            
            if (!hasLabel && !hasAriaLabel && !hasAriaLabelledby) {
                issues.push({
                    element: control.tagName + (control.id ? '#' + control.id : ''),
                    issue: '缺少标签',
                    suggestion: '添加<label>、aria-label或aria-labelledby'
                });
            }
        });
        
        // 检查图片
        const images = document.querySelectorAll('img');
        images.forEach(img => {
            if (!img.alt && img.role !== 'presentation') {
                issues.push({
                    element: 'img[src="' + img.src + '"]',
                    issue: '缺少alt文本',
                    suggestion: '添加描述性alt文本或role="presentation"'
                });
            }
        });
        
        // 检查按钮
        const buttons = document.querySelectorAll('button, [role="button"]');
        buttons.forEach(button => {
            const text = button.textContent.trim();
            const ariaLabel = button.getAttribute('aria-label');
            
            if (!text && !ariaLabel) {
                issues.push({
                    element: 'button',
                    issue: '按钮缺少可访问名称',
                    suggestion: '添加文本内容或aria-label'
                });
            }
        });
        
        return issues;
        """
        return driver.execute_script(script)
    
    def _check_aria_roles(self, driver):
        """检查ARIA角色的正确使用"""
        script = """
        const issues = [];
        const validRoles = ['button', 'navigation', 'main', 'banner', 'contentinfo', 
                           'form', 'search', 'menu', 'menuitem', 'tab', 'tabpanel'];
        
        // 检查无效角色
        const elementsWithRole = document.querySelectorAll('[role]');
        elementsWithRole.forEach(element => {
            const role = element.getAttribute('role');
            if (!validRoles.includes(role)) {
                issues.push({
                    element: element.tagName + '[role="' + role + '"]',
                    issue: '无效的ARIA角色',
                    suggestion: '使用有效的ARIA角色'
                });
            }
        });
        
        // 检查冗余角色
        const redundantRoles = {
            'button': 'button',
            'nav': 'navigation',
            'main': 'main',
            'header': 'banner',
            'footer': 'contentinfo'
        };
        
        Object.entries(redundantRoles).forEach(([tag, role]) => {
            const elements = document.querySelectorAll(tag + '[role="' + role + '"]');
            elements.forEach(element => {
                issues.push({
                    element: tag + '[role="' + role + '"]',
                    issue: '冗余的ARIA角色',
                    suggestion: '移除冗余的role属性'
                });
            });
        });
        
        return issues;
        """
        return driver.execute_script(script)
```

**2. 键盘导航测试**
```python
class KeyboardNavigationTester:
    """键盘导航测试器"""
    
    def __init__(self, driver):
        self.driver = driver
        self.tab_order = []
    
    def test_tab_navigation(self):
        """测试Tab键导航"""
        # 重置焦点到body
        self.driver.find_element(By.TAG_NAME, 'body').click()
        
        # 记录Tab顺序
        self.tab_order = []
        previous_element = None
        
        for i in range(50):  # 最多测试50个元素
            # 按Tab键
            ActionChains(self.driver).send_keys(Keys.TAB).perform()
            
            # 获取当前焦点元素
            current_element = self.driver.switch_to.active_element
            
            # 检查是否循环
            if current_element == previous_element:
                break
            
            # 记录元素信息
            element_info = self._get_element_info(current_element)
            self.tab_order.append(element_info)
            
            previous_element = current_element
        
        # 分析Tab顺序
        return self._analyze_tab_order()
    
    def _get_element_info(self, element):
        """获取元素信息"""
        return {
            'tag': element.tag_name,
            'id': element.get_attribute('id'),
            'class': element.get_attribute('class'),
            'tabindex': element.get_attribute('tabindex'),
            'visible': element.is_displayed(),
            'enabled': element.is_enabled(),
            'rect': element.rect
        }
    
    def _analyze_tab_order(self):
        """分析Tab顺序问题"""
        issues = []
        
        # 检查不可见元素
        invisible_focusable = [
            el for el in self.tab_order 
            if not el['visible']
        ]
        if invisible_focusable:
            issues.append({
                'type': 'invisible_focusable',
                'elements': invisible_focusable,
                'severity': 'high'
            })
        
        # 检查Tab顺序逻辑性
        if not self._is_logical_order():
            issues.append({
                'type': 'illogical_tab_order',
                'suggestion': '考虑调整tabindex或DOM顺序',
                'severity': 'medium'
            })
        
        # 检查跳过重要元素
        important_skipped = self._find_skipped_important_elements()
        if important_skipped:
            issues.append({
                'type': 'important_elements_skipped',
                'elements': important_skipped,
                'severity': 'high'
            })
        
        return {
            'tab_order': self.tab_order,
            'issues': issues,
            'total_focusable': len(self.tab_order)
        }
    
    def test_keyboard_interactions(self):
        """测试键盘交互"""
        test_results = {}
        
        # 测试下拉菜单
        test_results['dropdown'] = self._test_dropdown_keyboard()
        
        # 测试模态框
        test_results['modal'] = self._test_modal_keyboard()
        
        # 测试表格导航
        test_results['table'] = self._test_table_navigation()
        
        return test_results
    
    def _test_dropdown_keyboard(self):
        """测试下拉菜单的键盘操作"""
        dropdowns = self.driver.find_elements(
            By.CSS_SELECTOR, '[role="combobox"], select'
        )
        
        results = []
        for dropdown in dropdowns:
            dropdown.click()
            
            # 测试方向键
            can_navigate_with_arrows = self._test_arrow_navigation(dropdown)
            
            # 测试Enter选择
            can_select_with_enter = self._test_enter_selection(dropdown)
            
            # 测试Escape关闭
            can_close_with_escape = self._test_escape_close(dropdown)
            
            results.append({
                'element': self._get_element_identifier(dropdown),
                'arrow_navigation': can_navigate_with_arrows,
                'enter_selection': can_select_with_enter,
                'escape_close': can_close_with_escape
            })
        
        return results
```

**3. 颜色对比度测试**
```python
class ColorContrastTester:
    """颜色对比度测试器"""
    
    def test_color_contrast(self, driver):
        """测试所有文本的颜色对比度"""
        script = """
        function getLuminance(rgb) {
            const [r, g, b] = rgb.match(/\\d+/g).map(Number);
            const [rs, gs, bs] = [r, g, b].map(c => {
                c = c / 255;
                return c <= 0.03928 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
            });
            return 0.2126 * rs + 0.7152 * gs + 0.0722 * bs;
        }
        
        function getContrastRatio(color1, color2) {
            const lum1 = getLuminance(color1);
            const lum2 = getLuminance(color2);
            const brightest = Math.max(lum1, lum2);
            const darkest = Math.min(lum1, lum2);
            return (brightest + 0.05) / (darkest + 0.05);
        }
        
        const issues = [];
        const elements = document.querySelectorAll('*');
        
        elements.forEach(element => {
            const styles = window.getComputedStyle(element);
            const color = styles.color;
            const backgroundColor = styles.backgroundColor;
            
            // 跳过透明背景
            if (backgroundColor === 'rgba(0, 0, 0, 0)') return;
            
            const fontSize = parseFloat(styles.fontSize);
            const fontWeight = styles.fontWeight;
            const isLargeText = fontSize >= 18 || (fontSize >= 14 && fontWeight >= 700);
            
            const ratio = getContrastRatio(color, backgroundColor);
            const requiredRatio = isLargeText ? 3 : 4.5;
            
            if (ratio < requiredRatio) {
                issues.push({
                    element: element.tagName + (element.id ? '#' + element.id : ''),
                    color: color,
                    backgroundColor: backgroundColor,
                    ratio: ratio.toFixed(2),
                    requiredRatio: requiredRatio,
                    isLargeText: isLargeText
                });
            }
        });
        
        return issues;
        """
        return driver.execute_script(script)
```

**4. 屏幕阅读器兼容性测试**
```python
class ScreenReaderTester:
    """屏幕阅读器兼容性测试"""
    
    def test_screen_reader_compatibility(self, driver):
        """测试屏幕阅读器兼容性"""
        results = {
            'landmarks': self._test_landmarks(driver),
            'headings': self._test_heading_structure(driver),
            'live_regions': self._test_live_regions(driver),
            'form_structure': self._test_form_structure(driver)
        }
        
        return results
    
    def _test_landmarks(self, driver):
        """测试地标区域"""
        script = """
        const landmarks = {
            'main': document.querySelectorAll('main, [role="main"]').length,
            'navigation': document.querySelectorAll('nav, [role="navigation"]').length,
            'banner': document.querySelectorAll('header, [role="banner"]').length,
            'contentinfo': document.querySelectorAll('footer, [role="contentinfo"]').length,
            'search': document.querySelectorAll('[role="search"]').length,
            'form': document.querySelectorAll('form[aria-label], form[aria-labelledby], [role="form"]').length
        };
        
        const issues = [];
        
        if (landmarks.main === 0) {
            issues.push('缺少main地标');
        } else if (landmarks.main > 1) {
            issues.push('多个main地标，应该只有一个');
        }
        
        if (landmarks.navigation === 0) {
            issues.push('缺少navigation地标');
        }
        
        return {
            landmarks: landmarks,
            issues: issues
        };
        """
        return driver.execute_script(script)
    
    def _test_heading_structure(self, driver):
        """测试标题结构"""
        script = """
        const headings = [];
        const headingElements = document.querySelectorAll('h1, h2, h3, h4, h5, h6');
        
        headingElements.forEach(heading => {
            headings.push({
                level: parseInt(heading.tagName.charAt(1)),
                text: heading.textContent.trim(),
                visible: heading.offsetParent !== null
            });
        });
        
        const issues = [];
        
        // 检查是否有h1
        const h1Count = headings.filter(h => h.level === 1).length;
        if (h1Count === 0) {
            issues.push('页面缺少h1标题');
        } else if (h1Count > 1) {
            issues.push('页面有多个h1标题');
        }
        
        // 检查标题层级跳跃
        for (let i = 1; i < headings.length; i++) {
            const levelDiff = headings[i].level - headings[i-1].level;
            if (levelDiff > 1) {
                issues.push(`标题层级跳跃：从h${headings[i-1].level}到h${headings[i].level}`);
            }
        }
        
        return {
            headings: headings,
            issues: issues
        };
        """
        return driver.execute_script(script)
```

### 7.3.3 移动端可访问性

**1. 触摸目标测试**
```python
class TouchTargetTester:
    """触摸目标大小测试"""
    
    def test_touch_targets(self, driver):
        """测试触摸目标是否足够大"""
        script = """
        const minSize = 44; // WCAG推荐的最小触摸目标大小（像素）
        const issues = [];
        
        // 获取所有可交互元素
        const interactiveElements = document.querySelectorAll(
            'a, button, input, select, textarea, [role="button"], [onclick]'
        );
        
        interactiveElements.forEach(element => {
            const rect = element.getBoundingClientRect();
            const width = rect.width;
            const height = rect.height;
            
            if (width < minSize || height < minSize) {
                const styles = window.getComputedStyle(element);
                const padding = {
                    top: parseFloat(styles.paddingTop),
                    right: parseFloat(styles.paddingRight),
                    bottom: parseFloat(styles.paddingBottom),
                    left: parseFloat(styles.paddingLeft)
                };
                
                // 考虑内边距
                const effectiveWidth = width + padding.left + padding.right;
                const effectiveHeight = height + padding.top + padding.bottom;
                
                if (effectiveWidth < minSize || effectiveHeight < minSize) {
                    issues.push({
                        element: element.tagName + (element.id ? '#' + element.id : ''),
                        size: {width: width, height: height},
                        effectiveSize: {width: effectiveWidth, height: effectiveHeight},
                        text: element.textContent.trim().substring(0, 50)
                    });
                }
            }
        });
        
        return issues;
        """
        return driver.execute_script(script)
```

**2. 手势可访问性**
```python
class GestureAccessibilityTester:
    """手势可访问性测试"""
    
    def test_gesture_alternatives(self, driver):
        """测试复杂手势是否有替代方案"""
        # 检测使用触摸事件的元素
        script = """
        const elements = document.querySelectorAll('*');
        const gestureElements = [];
        
        elements.forEach(element => {
            const events = getEventListeners(element);
            const hasGestures = events && (
                events.touchstart || events.touchmove || events.touchend ||
                events.gesturestart || events.gesturechange || events.gestureend
            );
            
            if (hasGestures) {
                // 检查是否有替代的点击事件
                const hasClickAlternative = events.click || events.mousedown;
                
                gestureElements.push({
                    element: element.tagName + (element.id ? '#' + element.id : ''),
                    gestures: Object.keys(events).filter(e => e.includes('touch') || e.includes('gesture')),
                    hasAlternative: hasClickAlternative
                });
            }
        });
        
        return gestureElements;
        """
        
        # 注意：getEventListeners只在Chrome DevTools中可用
        # 实际测试中可能需要其他方法
        gesture_elements = self._detect_gesture_handlers(driver)
        
        issues = []
        for element in gesture_elements:
            if not element['hasAlternative']:
                issues.append({
                    'element': element['element'],
                    'gestures': element['gestures'],
                    'issue': '复杂手势缺少简单替代方案'
                })
        
        return issues
```

### 7.3.4 动态内容可访问性

**1. 实时区域测试**
```python
class LiveRegionTester:
    """实时区域（Live Region）测试"""
    
    def test_live_regions(self, driver):
        """测试动态内容的可访问性通知"""
        # 监控实时区域变化
        setup_script = """
        window.liveRegionChanges = [];
        
        // 监控所有实时区域
        const liveRegions = document.querySelectorAll('[aria-live], [role="alert"], [role="status"]');
        
        liveRegions.forEach(region => {
            const observer = new MutationObserver(mutations => {
                mutations.forEach(mutation => {
                    window.liveRegionChanges.push({
                        element: region.tagName + (region.id ? '#' + region.id : ''),
                        ariaLive: region.getAttribute('aria-live'),
                        role: region.getAttribute('role'),
                        type: mutation.type,
                        timestamp: Date.now(),
                        newContent: region.textContent
                    });
                });
            });
            
            observer.observe(region, {
                childList: true,
                characterData: true,
                subtree: true
            });
        });
        """
        driver.execute_script(setup_script)
        
        # 触发一些动态内容更新（根据具体应用）
        # ...
        
        # 收集结果
        time.sleep(2)  # 等待动态更新
        changes = driver.execute_script("return window.liveRegionChanges;")
        
        # 分析结果
        return self._analyze_live_region_changes(changes)
    
    def _analyze_live_region_changes(self, changes):
        """分析实时区域变化"""
        issues = []
        
        # 检查过于频繁的更新
        frequency_map = {}
        for change in changes:
            key = change['element']
            if key not in frequency_map:
                frequency_map[key] = []
            frequency_map[key].append(change['timestamp'])
        
        for element, timestamps in frequency_map.items():
            if len(timestamps) > 5:  # 2秒内超过5次更新
                issues.append({
                    'element': element,
                    'issue': '更新过于频繁',
                    'count': len(timestamps),
                    'suggestion': '考虑降低更新频率或使用aria-busy'
                })
        
        return {
            'changes': changes,
            'issues': issues
        }
```

### 7.3.5 表单可访问性

**1. 表单验证可访问性**
```python
class FormAccessibilityTester:
    """表单可访问性测试"""
    
    def test_form_accessibility(self, driver):
        """测试表单的可访问性"""
        forms = driver.find_elements(By.TAG_NAME, 'form')
        results = []
        
        for form in forms:
            form_id = form.get_attribute('id') or 'unnamed'
            result = {
                'form_id': form_id,
                'issues': []
            }
            
            # 测试表单结构
            result['issues'].extend(self._test_form_structure(form))
            
            # 测试错误处理
            result['issues'].extend(self._test_error_handling(form))
            
            # 测试必填字段标识
            result['issues'].extend(self._test_required_fields(form))
            
            results.append(result)
        
        return results
    
    def _test_form_structure(self, form):
        """测试表单结构"""
        issues = []
        
        # 检查fieldset和legend
        fieldsets = form.find_elements(By.TAG_NAME, 'fieldset')
        for fieldset in fieldsets:
            legends = fieldset.find_elements(By.TAG_NAME, 'legend')
            if len(legends) == 0:
                issues.append({
                    'element': 'fieldset',
                    'issue': 'fieldset缺少legend',
                    'severity': 'medium'
                })
        
        # 检查表单控件的标签关联
        inputs = form.find_elements(By.CSS_SELECTOR, 'input, select, textarea')
        for input_elem in inputs:
            input_id = input_elem.get_attribute('id')
            input_type = input_elem.get_attribute('type')
            
            # 跳过隐藏字段
            if input_type == 'hidden':
                continue
            
            # 检查标签
            has_label = False
            if input_id:
                labels = form.find_elements(By.CSS_SELECTOR, f'label[for="{input_id}"]')
                has_label = len(labels) > 0
            
            # 检查ARIA标签
            has_aria_label = input_elem.get_attribute('aria-label') is not None
            has_aria_labelledby = input_elem.get_attribute('aria-labelledby') is not None
            
            if not has_label and not has_aria_label and not has_aria_labelledby:
                issues.append({
                    'element': f'input[type="{input_type}"]',
                    'issue': '表单控件缺少可访问标签',
                    'severity': 'high'
                })
        
        return issues
    
    def _test_error_handling(self, form):
        """测试错误处理的可访问性"""
        script = """
        const form = arguments[0];
        const issues = [];
        
        // 查找错误消息
        const errorMessages = form.querySelectorAll('.error, .error-message, [role="alert"]');
        
        errorMessages.forEach(error => {
            // 检查错误消息是否与表单控件关联
            const associatedControl = error.getAttribute('aria-describedby') || 
                                    error.getAttribute('id');
            
            if (!associatedControl) {
                issues.push({
                    element: 'error message',
                    issue: '错误消息未与表单控件关联',
                    suggestion: '使用aria-describedby关联错误消息'
                });
            }
        });
        
        // 检查表单控件的错误状态
        const invalidControls = form.querySelectorAll('[aria-invalid="true"]');
        invalidControls.forEach(control => {
            const errorId = control.getAttribute('aria-describedby');
            if (!errorId || !form.querySelector('#' + errorId)) {
                issues.push({
                    element: control.tagName,
                    issue: '无效控件缺少错误描述',
                    suggestion: '添加aria-describedby指向错误消息'
                });
            }
        });
        
        return issues;
        """
        return self.driver.execute_script(script, form)
```

### 7.3.6 可访问性测试报告

```python
class AccessibilityReporter:
    """可访问性测试报告生成器"""
    
    def generate_report(self, test_results):
        """生成综合的可访问性测试报告"""
        report = {
            'summary': self._generate_summary(test_results),
            'wcag_compliance': self._assess_wcag_compliance(test_results),
            'detailed_issues': self._categorize_issues(test_results),
            'recommendations': self._generate_recommendations(test_results)
        }
        
        return report
    
    def _generate_summary(self, results):
        """生成摘要"""
        total_issues = sum(len(r.get('issues', [])) for r in results.values())
        
        severity_count = {
            'critical': 0,
            'high': 0,
            'medium': 0,
            'low': 0
        }
        
        for category_results in results.values():
            if isinstance(category_results, list):
                for item in category_results:
                    if 'severity' in item:
                        severity_count[item['severity']] += 1
        
        return {
            'total_issues': total_issues,
            'severity_distribution': severity_count,
            'tested_categories': list(results.keys())
        }
    
    def _assess_wcag_compliance(self, results):
        """评估WCAG合规性"""
        compliance_status = {
            'Level A': {
                'status': 'unknown',
                'issues': []
            },
            'Level AA': {
                'status': 'unknown',
                'issues': []
            },
            'Level AAA': {
                'status': 'unknown',
                'issues': []
            }
        }
        
        # 根据发现的问题评估合规级别
        # 这里需要根据具体的WCAG标准映射
        
        return compliance_status
    
    def generate_html_report(self, report, output_path):
        """生成HTML格式的报告"""
        html_template = """
        <!DOCTYPE html>
        <html lang="zh-CN">
        <head>
            <meta charset="UTF-8">
            <title>可访问性测试报告</title>
            <style>
                body { font-family: Arial, sans-serif; margin: 20px; }
                .summary { background: #f0f0f0; padding: 20px; border-radius: 5px; }
                .issue { margin: 10px 0; padding: 10px; border-left: 4px solid #ddd; }
                .critical { border-color: #d00; }
                .high { border-color: #f60; }
                .medium { border-color: #fc0; }
                .low { border-color: #09f; }
                table { border-collapse: collapse; width: 100%; }
                th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
            </style>
        </head>
        <body>
            <h1>可访问性测试报告</h1>
            <div class="summary">
                <h2>摘要</h2>
                <p>总问题数：{total_issues}</p>
                <p>严重等级分布：</p>
                <ul>
                    <li>严重：{critical_count}</li>
                    <li>高：{high_count}</li>
                    <li>中：{medium_count}</li>
                    <li>低：{low_count}</li>
                </ul>
            </div>
            
            <h2>详细问题列表</h2>
            {issues_section}
            
            <h2>建议</h2>
            {recommendations_section}
        </body>
        </html>
        """
        
        # 填充模板
        html_content = self._fill_template(html_template, report)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
```

### 练习 7.3

1. 设计一个测试策略来验证单页应用（SPA）的路由变化对屏幕阅读器的通知。

<details>
<summary>参考答案</summary>

SPA路由变化的可访问性测试策略：

```python
class SPARouteAccessibilityTester:
    """SPA路由变化可访问性测试"""
    
    def __init__(self, driver):
        self.driver = driver
        self.aria_monitor = ARIALiveRegionMonitor(driver)
    
    def test_route_announcements(self, test_routes):
        """测试路由变化是否正确通知屏幕阅读器"""
        results = []
        
        # 设置监控
        self.aria_monitor.start_monitoring()
        
        for route in test_routes:
            # 导航到路由
            self._navigate_to_route(route['path'])
            
            # 等待路由变化完成
            time.sleep(1)
            
            # 收集通知
            announcements = self.aria_monitor.get_announcements()
            
            # 验证结果
            validation = self._validate_route_announcement(route, announcements)
            
            results.append({
                'route': route,
                'announcements': announcements,
                'validation': validation
            })
            
            # 清除记录
            self.aria_monitor.clear()
        
        return results
    
    def _validate_route_announcement(self, route, announcements):
        """验证路由通知的正确性"""
        issues = []
        
        # 检查是否有通知
        if len(announcements) == 0:
            issues.append({
                'issue': '路由变化未产生任何通知',
                'severity': 'critical',
                'suggestion': '添加aria-live区域通知页面变化'
            })
            return issues
        
        # 检查通知内容
        has_page_title = any(
            route['expected_title'] in ann['content'] 
            for ann in announcements
        )
        
        if not has_page_title:
            issues.append({
                'issue': '通知中缺少页面标题',
                'severity': 'high',
                'suggestion': '在通知中包含新页面的标题'
            })
        
        # 检查通知时机
        for ann in announcements:
            if ann['delay'] > 1000:  # 超过1秒
                issues.append({
                    'issue': '通知延迟过长',
                    'delay': ann['delay'],
                    'severity': 'medium'
                })
        
        # 检查重复通知
        contents = [ann['content'] for ann in announcements]
        if len(contents) != len(set(contents)):
            issues.append({
                'issue': '存在重复通知',
                'severity': 'low'
            })
        
        return issues
    
    def test_focus_management(self, test_routes):
        """测试路由变化后的焦点管理"""
        results = []
        
        for route in test_routes:
            self._navigate_to_route(route['path'])
            time.sleep(0.5)
            
            # 获取当前焦点
            focused_element = self.driver.switch_to.active_element
            
            # 验证焦点位置
            focus_validation = self._validate_focus_placement(
                route, focused_element
            )
            
            results.append({
                'route': route,
                'focused_element': self._get_element_description(focused_element),
                'validation': focus_validation
            })
        
        return results
    
    def _validate_focus_placement(self, route, focused_element):
        """验证焦点位置是否合适"""
        issues = []
        
        # 检查焦点是否在body上（不理想）
        if focused_element.tag_name == 'body':
            issues.append({
                'issue': '焦点停留在body上',
                'severity': 'high',
                'suggestion': '将焦点移到主要内容或标题'
            })
        
        # 检查焦点是否可见
        if not focused_element.is_displayed():
            issues.append({
                'issue': '焦点在不可见元素上',
                'severity': 'critical'
            })
        
        # 检查是否跳过导航
        if route.get('skip_nav_expected', True):
            # 验证焦点是否在主要内容区域
            main_content = self.driver.find_element(By.CSS_SELECTOR, 'main, [role="main"]')
            if not self._is_descendant(focused_element, main_content):
                issues.append({
                    'issue': '焦点未跳过导航区域',
                    'severity': 'medium',
                    'suggestion': '实现跳过导航功能'
                })
        
        return issues
    
    def test_loading_states(self):
        """测试加载状态的可访问性"""
        # 注入延迟以捕获加载状态
        self.driver.execute_script("""
            // 拦截fetch以添加延迟
            const originalFetch = window.fetch;
            window.fetch = function(...args) {
                return new Promise(resolve => {
                    setTimeout(() => {
                        resolve(originalFetch.apply(this, args));
                    }, 2000); // 2秒延迟
                });
            };
        """)
        
        # 触发路由变化
        self._navigate_to_route('/slow-loading-page')
        
        # 立即检查加载指示器
        loading_indicator = self._find_loading_indicator()
        
        issues = []
        
        if not loading_indicator:
            issues.append({
                'issue': '缺少加载指示器',
                'severity': 'high'
            })
        else:
            # 验证加载指示器的可访问性
            aria_busy = loading_indicator.get_attribute('aria-busy')
            aria_live = loading_indicator.get_attribute('aria-live')
            role = loading_indicator.get_attribute('role')
            
            if aria_busy != 'true':
                issues.append({
                    'issue': '加载时未设置aria-busy="true"',
                    'severity': 'medium'
                })
            
            if not aria_live and role != 'status':
                issues.append({
                    'issue': '加载指示器缺少实时区域属性',
                    'severity': 'medium'
                })
        
        return issues

class ARIALiveRegionMonitor:
    """ARIA实时区域监控器"""
    
    def __init__(self, driver):
        self.driver = driver
        
    def start_monitoring(self):
        """开始监控实时区域"""
        script = """
        window.ariaAnnouncements = [];
        
        // 创建MutationObserver监控所有实时区域
        const observer = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                const target = mutation.target;
                const ariaLive = target.getAttribute('aria-live') || 
                               target.closest('[aria-live]')?.getAttribute('aria-live');
                const role = target.getAttribute('role') || 
                           target.closest('[role="status"], [role="alert"]')?.getAttribute('role');
                
                if (ariaLive || role === 'status' || role === 'alert') {
                    window.ariaAnnouncements.push({
                        content: target.textContent,
                        ariaLive: ariaLive,
                        role: role,
                        timestamp: Date.now(),
                        delay: Date.now() - window.lastRouteChange || 0
                    });
                }
            });
        });
        
        // 监控整个文档
        observer.observe(document.body, {
            childList: true,
            subtree: true,
            characterData: true
        });
        
        // 记录路由变化时间
        window.lastRouteChange = Date.now();
        """
        self.driver.execute_script(script)
    
    def get_announcements(self):
        """获取收集到的通知"""
        return self.driver.execute_script("return window.ariaAnnouncements || [];")
    
    def clear(self):
        """清除记录"""
        self.driver.execute_script("window.ariaAnnouncements = [];")
```

这个解决方案测试了：
1. 路由变化时的屏幕阅读器通知
2. 焦点管理和跳过导航
3. 加载状态的可访问性
4. 实时区域的正确使用
</details>

2. 如何测试复杂数据表格的可访问性，包括排序、筛选和分页功能？

<details>
<summary>参考答案</summary>

复杂数据表格可访问性测试：

```python
class ComplexTableAccessibilityTester:
    """复杂表格可访问性测试"""
    
    def __init__(self, driver):
        self.driver = driver
    
    def test_table_structure(self, table_selector):
        """测试表格结构的可访问性"""
        table = self.driver.find_element(By.CSS_SELECTOR, table_selector)
        
        results = {
            'structure': self._validate_table_structure(table),
            'headers': self._validate_headers(table),
            'navigation': self._test_keyboard_navigation(table),
            'sorting': self._test_sorting_accessibility(table),
            'filtering': self._test_filter_accessibility(table),
            'pagination': self._test_pagination_accessibility(table)
        }
        
        return results
    
    def _validate_table_structure(self, table):
        """验证表格基本结构"""
        issues = []
        
        # 检查caption
        captions = table.find_elements(By.TAG_NAME, 'caption')
        if len(captions) == 0:
            # 检查aria-label或aria-labelledby
            aria_label = table.get_attribute('aria-label')
            aria_labelledby = table.get_attribute('aria-labelledby')
            
            if not aria_label and not aria_labelledby:
                issues.append({
                    'issue': '表格缺少描述',
                    'severity': 'high',
                    'suggestion': '添加<caption>或aria-label'
                })
        
        # 检查thead, tbody结构
        thead = table.find_elements(By.TAG_NAME, 'thead')
        tbody = table.find_elements(By.TAG_NAME, 'tbody')
        
        if len(thead) == 0:
            issues.append({
                'issue': '缺少<thead>元素',
                'severity': 'medium'
            })
        
        if len(tbody) == 0:
            issues.append({
                'issue': '缺少<tbody>元素',
                'severity': 'medium'
            })
        
        return issues
    
    def _validate_headers(self, table):
        """验证表头的可访问性"""
        script = """
        const table = arguments[0];
        const issues = [];
        
        // 检查所有th元素
        const headers = table.querySelectorAll('th');
        headers.forEach((th, index) => {
            // 检查scope属性
            const scope = th.getAttribute('scope');
            const isColHeader = th.parentElement.parentElement.tagName === 'THEAD';
            
            if (!scope) {
                issues.push({
                    header: th.textContent,
                    issue: '缺少scope属性',
                    suggestion: isColHeader ? 'scope="col"' : 'scope="row"'
                });
            }
            
            // 检查排序功能的可访问性
            const sortButton = th.querySelector('button, [role="button"]');
            if (sortButton) {
                const ariaSort = th.getAttribute('aria-sort');
                if (!ariaSort) {
                    issues.push({
                        header: th.textContent,
                        issue: '可排序列缺少aria-sort',
                        suggestion: '添加aria-sort="none|ascending|descending"'
                    });
                }
                
                // 检查排序按钮的可访问标签
                const ariaLabel = sortButton.getAttribute('aria-label');
                if (!ariaLabel || !ariaLabel.includes(th.textContent)) {
                    issues.push({
                        header: th.textContent,
                        issue: '排序按钮缺少描述性标签',
                        suggestion: '添加包含列名的aria-label'
                    });
                }
            }
        });
        
        // 检查复杂表头（使用headers属性）
        const dataCells = table.querySelectorAll('td');
        let hasComplexHeaders = false;
        
        dataCells.forEach(td => {
            if (td.getAttribute('headers')) {
                hasComplexHeaders = true;
            }
        });
        
        // 如果有跨行/跨列的表头，应该使用headers属性
        const spanningHeaders = table.querySelectorAll('th[colspan], th[rowspan]');
        if (spanningHeaders.length > 0 && !hasComplexHeaders) {
            issues.push({
                issue: '复杂表头结构未使用headers属性',
                severity: 'high'
            });
        }
        
        return issues;
        """
        return self.driver.execute_script(script, table)
    
    def _test_keyboard_navigation(self, table):
        """测试键盘导航"""
        results = {
            'tab_navigation': [],
            'arrow_navigation': [],
            'issues': []
        }
        
        # 测试Tab导航
        table.click()
        focusable_elements = []
        
        for _ in range(20):  # 最多测试20个元素
            self.driver.switch_to.active_element.send_keys(Keys.TAB)
            current = self.driver.switch_to.active_element
            
            # 检查是否还在表格内
            if not self._is_descendant(current, table):
                break
            
            focusable_elements.append({
                'element': current.tag_name,
                'text': current.text[:50]
            })
        
        results['tab_navigation'] = focusable_elements
        
        # 测试方向键导航（如果支持）
        self._test_arrow_key_navigation(table, results)
        
        return results
    
    def _test_sorting_accessibility(self, table):
        """测试排序功能的可访问性"""
        sortable_headers = self.driver.execute_script("""
            const table = arguments[0];
            const headers = Array.from(table.querySelectorAll('th'));
            return headers.filter(th => {
                return th.querySelector('button, [role="button"]') || 
                       th.getAttribute('onclick') ||
                       th.style.cursor === 'pointer';
            }).map(th => ({
                text: th.textContent,
                index: headers.indexOf(th),
                ariaSort: th.getAttribute('aria-sort')
            }));
        """, table)
        
        issues = []
        
        for header in sortable_headers:
            # 点击排序
            th = table.find_elements(By.TAG_NAME, 'th')[header['index']]
            th.click()
            time.sleep(0.5)
            
            # 检查aria-sort更新
            new_aria_sort = th.get_attribute('aria-sort')
            if new_aria_sort == header['ariaSort']:
                issues.append({
                    'header': header['text'],
                    'issue': '排序后aria-sort未更新'
                })
            
            # 检查是否有状态通知
            live_announcement = self._check_live_announcement()
            if not live_announcement:
                issues.append({
                    'header': header['text'],
                    'issue': '排序变化未通知屏幕阅读器'
                })
        
        return issues
    
    def _test_filter_accessibility(self, table):
        """测试筛选功能的可访问性"""
        # 查找筛选控件
        filter_controls = self.driver.find_elements(
            By.CSS_SELECTOR, 
            'input[type="search"], input[placeholder*="filter"], input[placeholder*="search"]'
        )
        
        issues = []
        
        for filter_input in filter_controls:
            # 检查标签
            label = self._find_label_for_input(filter_input)
            if not label:
                issues.append({
                    'element': 'filter input',
                    'issue': '筛选输入框缺少标签'
                })
            
            # 测试筛选
            filter_input.clear()
            filter_input.send_keys('test')
            time.sleep(1)
            
            # 检查结果通知
            results_announcement = self._check_results_announcement()
            if not results_announcement:
                issues.append({
                    'issue': '筛选结果未通知',
                    'suggestion': '添加aria-live区域通知结果数量'
                })
            
            # 检查无结果状态
            filter_input.clear()
            filter_input.send_keys('xyz123unlikely')
            time.sleep(1)
            
            no_results_message = self._find_no_results_message()
            if no_results_message:
                role = no_results_message.get_attribute('role')
                if role != 'status':
                    issues.append({
                        'issue': '无结果消息缺少适当的role',
                        'suggestion': 'role="status"'
                    })
        
        return issues
    
    def _test_pagination_accessibility(self, table):
        """测试分页功能的可访问性"""
        # 查找分页控件
        pagination = self.driver.find_element(
            By.CSS_SELECTOR, 
            '.pagination, [role="navigation"][aria-label*="pagination"]'
        )
        
        issues = []
        
        # 检查分页导航的aria-label
        aria_label = pagination.get_attribute('aria-label')
        if not aria_label:
            issues.append({
                'issue': '分页导航缺少aria-label',
                'severity': 'high'
            })
        
        # 检查当前页标识
        current_page = pagination.find_element(
            By.CSS_SELECTOR, 
            '.active, [aria-current="page"]'
        )
        
        if not current_page.get_attribute('aria-current'):
            issues.append({
                'issue': '当前页缺少aria-current="page"',
                'severity': 'medium'
            })
        
        # 测试页面切换通知
        next_button = pagination.find_element(
            By.CSS_SELECTOR, 
            '[aria-label*="next"], .next'
        )
        
        if next_button.is_enabled():
            next_button.click()
            time.sleep(1)
            
            # 检查页面变化通知
            page_announcement = self._check_live_announcement()
            if not page_announcement or 'page' not in page_announcement.lower():
                issues.append({
                    'issue': '页面切换未通知',
                    'suggestion': '通知新页码和结果范围'
                })
            
            # 检查焦点管理
            focused = self.driver.switch_to.active_element
            if focused == next_button:
                issues.append({
                    'issue': '页面切换后焦点仍在分页按钮',
                    'suggestion': '将焦点移到表格或结果摘要'
                })
        
        return issues
    
    def _check_live_announcement(self):
        """检查是否有实时通知"""
        script = """
        const liveRegions = document.querySelectorAll('[aria-live], [role="status"], [role="alert"]');
        for (let region of liveRegions) {
            if (region.textContent.trim()) {
                return region.textContent;
            }
        }
        return null;
        """
        return self.driver.execute_script(script)
    
    def generate_recommendations(self, test_results):
        """生成改进建议"""
        recommendations = []
        
        # 基于测试结果生成具体建议
        all_issues = []
        for category, results in test_results.items():
            if isinstance(results, list):
                all_issues.extend(results)
        
        # 优先级排序
        critical_issues = [i for i in all_issues if i.get('severity') == 'critical']
        high_issues = [i for i in all_issues if i.get('severity') == 'high']
        
        if critical_issues:
            recommendations.append({
                'priority': '紧急',
                'title': '必须立即修复的问题',
                'items': critical_issues
            })
        
        if high_issues:
            recommendations.append({
                'priority': '高',
                'title': '应尽快修复的问题',
                'items': high_issues
            })
        
        # 通用建议
        recommendations.append({
            'priority': '建议',
            'title': '最佳实践',
            'items': [
                '定期使用屏幕阅读器测试表格',
                '确保所有交互元素可通过键盘访问',
                '为动态内容变化提供适当的通知',
                '在用户测试中包含残障用户'
            ]
        })
        
        return recommendations
```

这个解决方案全面测试了：
1. 表格结构和语义标记
2. 排序功能的可访问性
3. 筛选和搜索的反馈
4. 分页导航和状态管理
5. 键盘操作支持
</details>

### 进一步研究

- 自动化可访问性测试的局限性和人工测试的必要性
- AI在可访问性测试中的应用（如图像描述质量评估）
- 多模态界面（语音、手势）的可访问性测试
- 游戏和互动内容的可访问性测试策略
- 可访问性测试与性能测试的平衡

## 7.4 移动测试考虑

移动设备的普及从根本上改变了Web应用的设计和测试方式。移动测试不仅需要考虑不同的屏幕尺寸，还要处理触摸交互、设备能力差异、网络条件变化等独特挑战。

### 7.4.1 移动测试的核心挑战

**1. 设备碎片化**
- **屏幕尺寸**：从4英寸到12.9英寸的各种设备
- **分辨率差异**：标准屏到4K显示屏
- **设备像素比**：1x到3x甚至更高
- **操作系统版本**：iOS、Android的多个版本并存
- **浏览器差异**：Safari、Chrome、WebView等

**2. 交互模式差异**
- **触摸 vs 鼠标**：精度和操作方式完全不同
- **手势操作**：滑动、捏合、长按等
- **虚拟键盘**：占用屏幕空间，影响布局
- **设备方向**：横屏和竖屏的切换

**3. 性能限制**
- **处理器性能**：比桌面设备慢
- **内存限制**：可用内存更少
- **电池消耗**：需要考虑功耗
- **网络条件**：3G/4G/5G的不稳定性

### 7.4.2 响应式设计测试

```python
class ResponsiveDesignTester:
    """响应式设计测试器"""
    
    def __init__(self, driver):
        self.driver = driver
        self.breakpoints = {
            'xs': 320,   # 小手机
            'sm': 375,   # 标准手机
            'md': 768,   # 平板
            'lg': 1024,  # 大平板/小笔记本
            'xl': 1280,  # 桌面
            'xxl': 1920  # 大屏幕
        }
    
    def test_responsive_layout(self, url):
        """测试响应式布局"""
        results = {}
        
        for size_name, width in self.breakpoints.items():
            # 设置视口大小
            height = int(width * 1.5)  # 假设16:10的比例
            self.driver.set_window_size(width, height)
            self.driver.get(url)
            
            # 等待布局稳定
            self._wait_for_layout_stability()
            
            # 执行测试
            results[size_name] = {
                'viewport': {'width': width, 'height': height},
                'layout_issues': self._check_layout_issues(),
                'overflow_issues': self._check_overflow(),
                'readability': self._check_readability(),
                'touch_targets': self._check_touch_target_sizes()
            }
        
        return results
    
    def _check_layout_issues(self):
        """检查布局问题"""
        script = """
        const issues = [];
        const viewportWidth = window.innerWidth;
        const viewportHeight = window.innerHeight;
        
        // 检查水平溢出
        if (document.documentElement.scrollWidth > viewportWidth) {
            issues.push({
                type: 'horizontal_overflow',
                scrollWidth: document.documentElement.scrollWidth,
                viewportWidth: viewportWidth
            });
        }
        
        // 检查元素重叠
        const elements = document.querySelectorAll('*');
        const positions = new Map();
        
        elements.forEach(el => {
            const rect = el.getBoundingClientRect();
            if (rect.width > 0 && rect.height > 0) {
                const key = `${Math.round(rect.top)},${Math.round(rect.left)}`;
                if (positions.has(key)) {
                    const existing = positions.get(key);
                    if (!el.contains(existing) && !existing.contains(el)) {
                        issues.push({
                            type: 'element_overlap',
                            element1: existing.tagName,
                            element2: el.tagName
                        });
                    }
                }
                positions.set(key, el);
            }
        });
        
        // 检查文本截断
        const textElements = document.querySelectorAll('p, h1, h2, h3, h4, h5, h6, span, div');
        textElements.forEach(el => {
            if (el.scrollWidth > el.clientWidth) {
                issues.push({
                    type: 'text_truncation',
                    element: el.tagName,
                    text: el.textContent.substring(0, 50)
                });
            }
        });
        
        return issues;
        """
        return self.driver.execute_script(script)
    
    def _check_touch_target_sizes(self):
        """检查触摸目标大小"""
        script = """
        const minSize = 44; // Apple建议的最小触摸目标
        const issues = [];
        
        const interactiveElements = document.querySelectorAll(
            'a, button, input, select, textarea, [onclick], [role="button"]'
        );
        
        interactiveElements.forEach(el => {
            const rect = el.getBoundingClientRect();
            if (rect.width < minSize || rect.height < minSize) {
                // 检查是否有足够的内边距
                const styles = window.getComputedStyle(el);
                const totalWidth = rect.width + 
                    parseFloat(styles.paddingLeft) + 
                    parseFloat(styles.paddingRight);
                const totalHeight = rect.height + 
                    parseFloat(styles.paddingTop) + 
                    parseFloat(styles.paddingBottom);
                
                if (totalWidth < minSize || totalHeight < minSize) {
                    issues.push({
                        element: el.tagName,
                        size: {width: rect.width, height: rect.height},
                        text: el.textContent || el.value || el.placeholder
                    });
                }
            }
        });
        
        return issues;
        """
        return self.driver.execute_script(script)
```

### 7.4.3 触摸交互测试

```python
class TouchInteractionTester:
    """触摸交互测试器"""
    
    def __init__(self, driver):
        self.driver = driver
        self.touch_actions = TouchActions(driver)
    
    def test_touch_gestures(self, element):
        """测试各种触摸手势"""
        results = {
            'tap': self._test_tap(element),
            'double_tap': self._test_double_tap(element),
            'long_press': self._test_long_press(element),
            'swipe': self._test_swipe(element),
            'pinch_zoom': self._test_pinch_zoom(element)
        }
        return results
    
    def _test_tap(self, element):
        """测试点击"""
        try:
            # 记录初始状态
            initial_state = self._capture_element_state(element)
            
            # 执行点击
            self.touch_actions.tap(element).perform()
            
            # 等待响应
            time.sleep(0.5)
            
            # 检查状态变化
            final_state = self._capture_element_state(element)
            
            return {
                'success': True,
                'response_time': self._measure_response_time(element),
                'state_changed': initial_state != final_state
            }
        except Exception as e:
            return {
                'success': False,
                'error': str(e)
            }
    
    def _test_swipe(self, element):
        """测试滑动"""
        # 获取元素位置和大小
        location = element.location
        size = element.size
        
        # 计算滑动起点和终点
        start_x = location['x'] + size['width'] * 0.8
        start_y = location['y'] + size['height'] * 0.5
        end_x = location['x'] + size['width'] * 0.2
        end_y = start_y
        
        # 执行滑动
        self.touch_actions.tap_and_hold(start_x, start_y)
        self.touch_actions.move(end_x, end_y)
        self.touch_actions.release(end_x, end_y)
        self.touch_actions.perform()
        
        # 验证滑动效果
        return self._verify_swipe_effect(element)
    
    def test_virtual_keyboard_impact(self):
        """测试虚拟键盘对布局的影响"""
        # 查找所有输入框
        inputs = self.driver.find_elements(By.CSS_SELECTOR, 
            'input[type="text"], input[type="email"], textarea')
        
        issues = []
        
        for input_field in inputs:
            # 记录键盘弹出前的布局
            self._scroll_to_element(input_field)
            before_layout = self._capture_viewport_layout()
            
            # 点击输入框触发键盘
            input_field.click()
            time.sleep(1)  # 等待键盘动画
            
            # 记录键盘弹出后的布局
            after_layout = self._capture_viewport_layout()
            
            # 分析影响
            impact = self._analyze_keyboard_impact(before_layout, after_layout, input_field)
            if impact['issues']:
                issues.extend(impact['issues'])
            
            # 关闭键盘
            self.driver.execute_script("document.activeElement.blur();")
            
        return issues
    
    def _analyze_keyboard_impact(self, before, after, input_element):
        """分析虚拟键盘的影响"""
        issues = []
        
        # 检查输入框是否仍然可见
        input_rect = input_element.rect
        viewport_height = self.driver.execute_script("return window.innerHeight;")
        
        if input_rect['y'] + input_rect['height'] > viewport_height:
            issues.append({
                'type': 'input_hidden_by_keyboard',
                'element': input_element.get_attribute('name') or 'unnamed input'
            })
        
        # 检查是否有重要内容被遮挡
        # 比较布局变化
        for element_id, before_pos in before.items():
            if element_id in after:
                after_pos = after[element_id]
                if after_pos['visible'] != before_pos['visible']:
                    issues.append({
                        'type': 'element_visibility_changed',
                        'element': element_id,
                        'was_visible': before_pos['visible'],
                        'is_visible': after_pos['visible']
                    })
        
        return {'issues': issues}
```

### 7.4.4 设备特性测试

```python
class DeviceFeatureTester:
    """设备特性测试器"""
    
    def test_device_orientation(self):
        """测试设备方向切换"""
        results = {
            'portrait_to_landscape': self._test_orientation_change('portrait', 'landscape'),
            'landscape_to_portrait': self._test_orientation_change('landscape', 'portrait')
        }
        return results
    
    def _test_orientation_change(self, from_orientation, to_orientation):
        """测试方向切换"""
        # 设置初始方向
        self._set_orientation(from_orientation)
        time.sleep(1)
        
        # 捕获初始状态
        initial_layout = self._capture_layout_metrics()
        
        # 切换方向
        self._set_orientation(to_orientation)
        time.sleep(1)  # 等待动画完成
        
        # 捕获切换后状态
        final_layout = self._capture_layout_metrics()
        
        # 分析结果
        return {
            'layout_adapted': self._verify_layout_adaptation(initial_layout, final_layout),
            'content_visible': self._check_content_visibility(),
            'navigation_accessible': self._check_navigation_accessibility()
        }
    
    def test_network_conditions(self):
        """测试不同网络条件下的表现"""
        network_profiles = {
            '3G': {
                'offline': False,
                'latency': 100,
                'download_throughput': 1.6 * 1024 * 1024 / 8,
                'upload_throughput': 750 * 1024 / 8
            },
            '4G': {
                'offline': False,
                'latency': 50,
                'download_throughput': 4 * 1024 * 1024 / 8,
                'upload_throughput': 3 * 1024 * 1024 / 8
            },
            'Offline': {
                'offline': True,
                'latency': 0,
                'download_throughput': 0,
                'upload_throughput': 0
            }
        }
        
        results = {}
        
        for network_name, conditions in network_profiles.items():
            self.driver.set_network_conditions(**conditions)
            
            results[network_name] = {
                'page_load_time': self._measure_page_load_time(),
                'resource_loading': self._check_resource_loading(),
                'offline_capability': self._test_offline_functionality() if conditions['offline'] else None
            }
        
        return results
    
    def test_touch_pressure(self):
        """测试压力感应（如3D Touch）"""
        script = """
        let supportsPressure = false;
        let maxPressure = 0;
        
        // 检测压力感应支持
        const checkPressure = (e) => {
            if (e.force > 0 || e.webkitForce > 0) {
                supportsPressure = true;
                maxPressure = Math.max(maxPressure, e.force || e.webkitForce);
            }
        };
        
        document.addEventListener('touchstart', checkPressure);
        document.addEventListener('touchmove', checkPressure);
        
        // 返回检测结果
        return new Promise(resolve => {
            setTimeout(() => {
                document.removeEventListener('touchstart', checkPressure);
                document.removeEventListener('touchmove', checkPressure);
                resolve({
                    supportsPressure,
                    maxPressure
                });
            }, 2000);
        });
        """
        return self.driver.execute_async_script(script)
```

### 7.4.5 移动性能测试

```python
class MobilePerformanceTester:
    """移动性能测试器"""
    
    def test_scroll_performance(self):
        """测试滚动性能"""
        # 启用性能监控
        self.driver.execute_script("""
            window.scrollPerfData = {
                frameCount: 0,
                droppedFrames: 0,
                startTime: performance.now()
            };
            
            let lastFrameTime = performance.now();
            
            function measureFrame() {
                const now = performance.now();
                const frameDuration = now - lastFrameTime;
                
                window.scrollPerfData.frameCount++;
                
                // 检测掉帧（超过16.67ms表示低于60fps）
                if (frameDuration > 16.67) {
                    window.scrollPerfData.droppedFrames++;
                }
                
                lastFrameTime = now;
                requestAnimationFrame(measureFrame);
            }
            
            requestAnimationFrame(measureFrame);
        """)
        
        # 执行滚动测试
        self._perform_scroll_test()
        
        # 收集性能数据
        perf_data = self.driver.execute_script("""
            const data = window.scrollPerfData;
            const duration = performance.now() - data.startTime;
            return {
                fps: (data.frameCount / duration) * 1000,
                droppedFrames: data.droppedFrames,
                smoothness: 1 - (data.droppedFrames / data.frameCount)
            };
        """)
        
        return perf_data
    
    def _perform_scroll_test(self):
        """执行滚动测试"""
        # 滚动到底部
        for _ in range(10):
            self.driver.execute_script("window.scrollBy(0, window.innerHeight / 2);")
            time.sleep(0.1)
        
        # 滚动到顶部
        for _ in range(10):
            self.driver.execute_script("window.scrollBy(0, -window.innerHeight / 2);")
            time.sleep(0.1)
    
    def test_animation_performance(self):
        """测试动画性能"""
        script = """
        // 查找所有动画元素
        const animatedElements = Array.from(document.querySelectorAll('*'))
            .filter(el => {
                const styles = getComputedStyle(el);
                return styles.animation !== 'none' || 
                       styles.transition !== 'none 0s ease 0s';
            });
        
        // 监控动画性能
        const observer = new PerformanceObserver((list) => {
            for (const entry of list.getEntries()) {
                if (entry.entryType === 'paint' || entry.entryType === 'layout') {
                    window.animationPerfData = window.animationPerfData || [];
                    window.animationPerfData.push({
                        type: entry.entryType,
                        duration: entry.duration,
                        timestamp: entry.startTime
                    });
                }
            }
        });
        
        observer.observe({ entryTypes: ['paint', 'layout'] });
        
        // 触发动画
        animatedElements.forEach(el => {
            el.style.transform = 'translateX(10px)';
            setTimeout(() => {
                el.style.transform = '';
            }, 100);
        });
        
        return animatedElements.length;
        """
        
        animated_count = self.driver.execute_script(script)
        time.sleep(2)  # 等待动画完成
        
        # 收集性能数据
        perf_data = self.driver.execute_script("return window.animationPerfData || [];")
        
        return {
            'animated_elements': animated_count,
            'performance_metrics': self._analyze_animation_performance(perf_data)
        }
    
    def test_memory_usage(self):
        """测试内存使用情况"""
        if self.driver.capabilities.get('browserName') == 'chrome':
            # Chrome特定的内存监控
            memory_info = self.driver.execute_script("""
                if (performance.memory) {
                    return {
                        usedJSHeapSize: performance.memory.usedJSHeapSize,
                        totalJSHeapSize: performance.memory.totalJSHeapSize,
                        jsHeapSizeLimit: performance.memory.jsHeapSizeLimit
                    };
                }
                return null;
            """)
            
            if memory_info:
                return {
                    'used_heap_mb': memory_info['usedJSHeapSize'] / 1024 / 1024,
                    'total_heap_mb': memory_info['totalJSHeapSize'] / 1024 / 1024,
                    'heap_limit_mb': memory_info['jsHeapSizeLimit'] / 1024 / 1024,
                    'usage_percentage': (memory_info['usedJSHeapSize'] / 
                                       memory_info['jsHeapSizeLimit']) * 100
                }
        
        return {'error': 'Memory monitoring not available'}
```

### 7.4.6 移动端特定功能测试

```python
class MobileSpecificFeatureTester:
    """移动端特定功能测试"""
    
    def test_viewport_configuration(self):
        """测试viewport配置"""
        viewport_meta = self.driver.execute_script("""
            const viewport = document.querySelector('meta[name="viewport"]');
            return viewport ? viewport.content : null;
        """)
        
        issues = []
        
        if not viewport_meta:
            issues.append({
                'type': 'missing_viewport',
                'severity': 'critical',
                'suggestion': '添加<meta name="viewport" content="width=device-width, initial-scale=1">'
            })
        else:
            # 解析viewport设置
            settings = dict(item.split('=') for item in viewport_meta.split(',') 
                          if '=' in item)
            
            # 检查关键设置
            if 'width' not in settings:
                issues.append({
                    'type': 'missing_width',
                    'severity': 'high'
                })
            
            if 'user-scalable' in settings and settings['user-scalable'] == 'no':
                issues.append({
                    'type': 'zoom_disabled',
                    'severity': 'medium',
                    'suggestion': '考虑允许用户缩放以提高可访问性'
                })
        
        return {
            'viewport_content': viewport_meta,
            'issues': issues
        }
    
    def test_touch_event_handling(self):
        """测试触摸事件处理"""
        script = """
        const touchElements = [];
        const allElements = document.querySelectorAll('*');
        
        allElements.forEach(el => {
            // 检查是否有触摸事件监听器
            const hasTouchStart = el.ontouchstart !== null;
            const hasTouchMove = el.ontouchmove !== null;
            const hasTouchEnd = el.ontouchend !== null;
            
            // 检查是否有对应的鼠标事件作为后备
            const hasMouseDown = el.onmousedown !== null || el.onclick !== null;
            
            if (hasTouchStart || hasTouchMove || hasTouchEnd) {
                touchElements.push({
                    tagName: el.tagName,
                    id: el.id,
                    hasTouchEvents: true,
                    hasMouseFallback: hasMouseDown,
                    touchEvents: {
                        touchstart: hasTouchStart,
                        touchmove: hasTouchMove,
                        touchend: hasTouchEnd
                    }
                });
            }
        });
        
        return touchElements;
        """
        
        touch_elements = self.driver.execute_script(script)
        
        issues = []
        for element in touch_elements:
            if not element['hasMouseFallback']:
                issues.append({
                    'element': element['tagName'] + (f"#{element['id']}" if element['id'] else ''),
                    'issue': '触摸事件缺少鼠标事件后备',
                    'severity': 'high'
                })
        
        return {
            'touch_enabled_elements': len(touch_elements),
            'issues': issues
        }
    
    def test_safe_area_handling(self):
        """测试安全区域处理（如iPhone刘海屏）"""
        script = """
        const styles = getComputedStyle(document.documentElement);
        
        // 检查是否使用了安全区域CSS变量
        const safeAreaInsets = {
            top: styles.getPropertyValue('padding-top').includes('safe-area-inset-top'),
            right: styles.getPropertyValue('padding-right').includes('safe-area-inset-right'),
            bottom: styles.getPropertyValue('padding-bottom').includes('safe-area-inset-bottom'),
            left: styles.getPropertyValue('padding-left').includes('safe-area-inset-left')
        };
        
        // 检查是否有viewport-fit=cover
        const viewport = document.querySelector('meta[name="viewport"]');
        const hasViewportFit = viewport && viewport.content.includes('viewport-fit=cover');
        
        // 检查关键UI元素是否避开了安全区域
        const fixedElements = document.querySelectorAll('[style*="position: fixed"]');
        const issues = [];
        
        fixedElements.forEach(el => {
            const rect = el.getBoundingClientRect();
            const styles = getComputedStyle(el);
            
            // 检查顶部固定元素
            if (rect.top < 44 && !styles.paddingTop.includes('safe-area')) {
                issues.push({
                    element: el.tagName,
                    issue: '顶部固定元素可能被刘海遮挡'
                });
            }
            
            // 检查底部固定元素
            if (rect.bottom > window.innerHeight - 34 && 
                !styles.paddingBottom.includes('safe-area')) {
                issues.push({
                    element: el.tagName,
                    issue: '底部固定元素可能被Home指示器遮挡'
                });
            }
        });
        
        return {
            safeAreaInsets,
            hasViewportFit,
            issues
        };
        """
        
        return self.driver.execute_script(script)
```

### 练习 7.4

1. 设计一个测试策略来验证PWA（渐进式Web应用）在移动设备上的安装和运行。

<details>
<summary>参考答案</summary>

PWA移动端测试策略：

```python
class PWAMobileTester:
    """PWA移动端测试器"""
    
    def __init__(self, driver):
        self.driver = driver
    
    def test_pwa_installability(self, url):
        """测试PWA可安装性"""
        self.driver.get(url)
        
        results = {
            'manifest': self._test_manifest(),
            'service_worker': self._test_service_worker(),
            'https': self._test_https(),
            'install_prompt': self._test_install_prompt(),
            'offline_capability': self._test_offline_mode(),
            'app_experience': self._test_app_like_experience()
        }
        
        return results
    
    def _test_manifest(self):
        """测试manifest文件"""
        script = """
        const link = document.querySelector('link[rel="manifest"]');
        if (!link) return { exists: false };
        
        return fetch(link.href)
            .then(res => res.json())
            .then(manifest => ({
                exists: true,
                valid: true,
                content: manifest,
                issues: this.validateManifest(manifest)
            }))
            .catch(err => ({
                exists: true,
                valid: false,
                error: err.message
            }));
        
        function validateManifest(manifest) {
            const issues = [];
            
            // 必需字段检查
            if (!manifest.name) issues.push('缺少name字段');
            if (!manifest.short_name) issues.push('缺少short_name字段');
            if (!manifest.start_url) issues.push('缺少start_url字段');
            if (!manifest.display) issues.push('缺少display字段');
            
            // 图标检查
            if (!manifest.icons || manifest.icons.length === 0) {
                issues.push('缺少图标');
            } else {
                const has192 = manifest.icons.some(i => i.sizes.includes('192'));
                const has512 = manifest.icons.some(i => i.sizes.includes('512'));
                if (!has192) issues.push('缺少192x192图标');
                if (!has512) issues.push('缺少512x512图标');
            }
            
            // 主题颜色检查
            if (!manifest.theme_color) issues.push('建议添加theme_color');
            if (!manifest.background_color) issues.push('建议添加background_color');
            
            return issues;
        }
        """
        
        return self.driver.execute_async_script(script)
    
    def _test_service_worker(self):
        """测试Service Worker"""
        script = """
        return new Promise(resolve => {
            if ('serviceWorker' in navigator) {
                navigator.serviceWorker.getRegistrations()
                    .then(registrations => {
                        if (registrations.length > 0) {
                            const sw = registrations[0];
                            resolve({
                                registered: true,
                                scope: sw.scope,
                                active: sw.active !== null,
                                waiting: sw.waiting !== null,
                                installing: sw.installing !== null
                            });
                        } else {
                            resolve({ registered: false });
                        }
                    });
            } else {
                resolve({ supported: false });
            }
        });
        """
        
        return self.driver.execute_async_script(script)
    
    def _test_install_prompt(self):
        """测试安装提示"""
        script = """
        window.deferredPrompt = null;
        window.installPromptFired = false;
        
        window.addEventListener('beforeinstallprompt', (e) => {
            e.preventDefault();
            window.deferredPrompt = e;
            window.installPromptFired = true;
        });
        
        // 等待一段时间看是否触发
        return new Promise(resolve => {
            setTimeout(() => {
                resolve({
                    promptAvailable: window.installPromptFired,
                    canPrompt: window.deferredPrompt !== null
                });
            }, 3000);
        });
        """
        
        return self.driver.execute_async_script(script)
    
    def _test_offline_mode(self):
        """测试离线模式"""
        # 先访问页面确保缓存
        self.driver.get(self.driver.current_url)
        time.sleep(2)
        
        # 切换到离线模式
        self.driver.set_network_conditions(offline=True, latency=0, 
                                         download_throughput=0, upload_throughput=0)
        
        # 刷新页面
        self.driver.refresh()
        time.sleep(2)
        
        # 检查页面是否正常加载
        offline_result = {
            'page_loads': self._check_page_loads(),
            'content_available': self._check_content_availability(),
            'offline_message': self._check_offline_message()
        }
        
        # 恢复网络
        self.driver.set_network_conditions(offline=False, latency=5,
                                         download_throughput=500 * 1024,
                                         upload_throughput=500 * 1024)
        
        return offline_result
    
    def _test_app_like_experience(self):
        """测试类应用体验"""
        # 模拟从主屏幕启动
        script = """
        // 检查是否处于standalone模式
        const isStandalone = window.matchMedia('(display-mode: standalone)').matches ||
                           window.navigator.standalone === true;
        
        // 检查状态栏样式
        const metaStatusBar = document.querySelector('meta[name="apple-mobile-web-app-status-bar-style"]');
        const metaCapable = document.querySelector('meta[name="apple-mobile-web-app-capable"]');
        
        // 检查是否禁用了某些浏览器UI特性
        const hasFullscreen = document.documentElement.requestFullscreen !== undefined;
        
        return {
            isStandalone,
            statusBarStyle: metaStatusBar ? metaStatusBar.content : null,
            webAppCapable: metaCapable ? metaCapable.content : null,
            hasFullscreen,
            themeColor: document.querySelector('meta[name="theme-color"]')?.content
        };
        """
        
        return self.driver.execute_script(script)
    
    def test_pwa_performance(self):
        """测试PWA性能指标"""
        # 使用Lighthouse API或Performance API
        script = """
        const metrics = {
            firstPaint: null,
            firstContentfulPaint: null,
            largestContentfulPaint: null,
            timeToInteractive: null
        };
        
        // 获取性能指标
        const perfObserver = new PerformanceObserver((list) => {
            for (const entry of list.getEntries()) {
                if (entry.name === 'first-paint') {
                    metrics.firstPaint = entry.startTime;
                } else if (entry.name === 'first-contentful-paint') {
                    metrics.firstContentfulPaint = entry.startTime;
                }
            }
        });
        
        perfObserver.observe({ entryTypes: ['paint'] });
        
        // LCP
        new PerformanceObserver((list) => {
            const entries = list.getEntries();
            metrics.largestContentfulPaint = entries[entries.length - 1].startTime;
        }).observe({ entryTypes: ['largest-contentful-paint'] });
        
        return new Promise(resolve => {
            setTimeout(() => resolve(metrics), 5000);
        });
        """
        
        return self.driver.execute_async_script(script)
    
    def test_push_notifications(self):
        """测试推送通知权限"""
        script = """
        if ('Notification' in window && 'serviceWorker' in navigator) {
            return {
                supported: true,
                permission: Notification.permission,
                pushManager: 'PushManager' in window
            };
        }
        return { supported: false };
        """
        
        return self.driver.execute_script(script)
```
</details>

2. 如何设计一个测试来验证移动Web应用在低端设备上的性能表现？

<details>
<summary>参考答案</summary>

低端设备性能测试设计：

```python
class LowEndDevicePerformanceTester:
    """低端设备性能测试器"""
    
    def __init__(self, driver):
        self.driver = driver
        
    def simulate_low_end_device(self):
        """模拟低端设备环境"""
        # CPU节流（6x slowdown）
        self.driver.execute_cdp_cmd('Emulation.setCPUThrottlingRate', {'rate': 6})
        
        # 网络节流（3G）
        self.driver.set_network_conditions(
            offline=False,
            latency=300,  # 300ms延迟
            download_throughput=1.6 * 1024 * 1024 / 8,  # 1.6 Mbps
            upload_throughput=750 * 1024 / 8  # 750 Kbps
        )
        
        # 内存限制（通过Chrome flags在启动时设置）
        # --max_old_space_size=512
    
    def test_low_end_performance(self, url):
        """测试低端设备性能"""
        self.simulate_low_end_device()
        
        results = {
            'loading_performance': self._test_loading_performance(url),
            'runtime_performance': self._test_runtime_performance(),
            'memory_pressure': self._test_memory_pressure(),
            'interaction_responsiveness': self._test_interaction_responsiveness()
        }
        
        return results
    
    def _test_loading_performance(self, url):
        """测试加载性能"""
        # 清除缓存
        self.driver.delete_all_cookies()
        self.driver.execute_script("window.localStorage.clear();")
        
        # 开始性能记录
        self.driver.execute_cdp_cmd('Performance.enable', {})
        
        # 标记开始时间
        start_time = time.time()
        
        # 加载页面
        self.driver.get(url)
        
        # 等待页面完全加载
        self.driver.execute_script("""
            return new Promise(resolve => {
                if (document.readyState === 'complete') {
                    resolve();
                } else {
                    window.addEventListener('load', resolve);
                }
            });
        """)
        
        load_time = time.time() - start_time
        
        # 获取性能指标
        metrics = self.driver.execute_script("""
            const perfData = performance.getEntriesByType('navigation')[0];
            const paintData = performance.getEntriesByType('paint');
            
            return {
                domContentLoaded: perfData.domContentLoadedEventEnd - perfData.domContentLoadedEventStart,
                loadComplete: perfData.loadEventEnd - perfData.loadEventStart,
                firstPaint: paintData.find(p => p.name === 'first-paint')?.startTime,
                firstContentfulPaint: paintData.find(p => p.name === 'first-contentful-paint')?.startTime,
                resources: performance.getEntriesByType('resource').length
            };
        """)
        
        # 获取关键资源
        critical_resources = self.driver.execute_script("""
            return performance.getEntriesByType('resource')
                .filter(r => r.initiatorType === 'script' || r.initiatorType === 'link')
                .map(r => ({
                    name: r.name.split('/').pop(),
                    duration: r.duration,
                    size: r.transferSize
                }))
                .sort((a, b) => b.duration - a.duration)
                .slice(0, 10);
        """)
        
        return {
            'total_load_time': load_time,
            'metrics': metrics,
            'critical_resources': critical_resources,
            'performance_score': self._calculate_performance_score(metrics, load_time)
        }
    
    def _test_runtime_performance(self):
        """测试运行时性能"""
        # 监控主线程阻塞
        script = """
        window.longTasks = [];
        
        const observer = new PerformanceObserver((list) => {
            for (const entry of list.getEntries()) {
                window.longTasks.push({
                    duration: entry.duration,
                    startTime: entry.startTime,
                    name: entry.name
                });
            }
        });
        
        observer.observe({ entryTypes: ['longtask'] });
        
        // 触发一些交互
        document.body.click();
        window.scrollTo(0, document.body.scrollHeight / 2);
        
        return new Promise(resolve => {
            setTimeout(() => {
                resolve(window.longTasks);
            }, 5000);
        });
        """
        
        long_tasks = self.driver.execute_async_script(script)
        
        # 计算阻塞指标
        total_blocking_time = sum(max(0, task['duration'] - 50) for task in long_tasks)
        
        # 测试滚动流畅度
        scroll_performance = self._test_scroll_smoothness()
        
        return {
            'long_tasks': len(long_tasks),
            'total_blocking_time': total_blocking_time,
            'worst_task': max(long_tasks, key=lambda x: x['duration']) if long_tasks else None,
            'scroll_performance': scroll_performance
        }
    
    def _test_memory_pressure(self):
        """测试内存压力下的表现"""
        # 执行一些内存密集操作
        script = """
        const results = {
            initial: performance.memory ? performance.memory.usedJSHeapSize : null,
            peak: 0,
            final: 0,
            gcCount: 0
        };
        
        // 监控GC
        if (performance.measureUserAgentSpecificMemory) {
            performance.measureUserAgentSpecificMemory().then(measurement => {
                results.detailed = measurement;
            });
        }
        
        // 创建一些内存压力
        const arrays = [];
        for (let i = 0; i < 10; i++) {
            arrays.push(new Array(100000).fill(Math.random()));
            if (performance.memory) {
                results.peak = Math.max(results.peak, performance.memory.usedJSHeapSize);
            }
        }
        
        // 触发一些DOM操作
        for (let i = 0; i < 100; i++) {
            const div = document.createElement('div');
            div.innerHTML = '<p>Test content ' + i + '</p>';
            document.body.appendChild(div);
        }
        
        // 清理
        arrays.length = 0;
        document.body.innerHTML = document.body.innerHTML;
        
        setTimeout(() => {
            if (performance.memory) {
                results.final = performance.memory.usedJSHeapSize;
            }
        }, 1000);
        
        return results;
        """
        
        memory_results = self.driver.execute_script(script)
        
        return {
            'memory_usage': memory_results,
            'memory_leak_risk': self._assess_memory_leak_risk(memory_results)
        }
    
    def _test_interaction_responsiveness(self):
        """测试交互响应性"""
        interactions = [
            {'type': 'click', 'selector': 'button, a', 'metric': 'first-input-delay'},
            {'type': 'input', 'selector': 'input[type="text"]', 'metric': 'input-delay'},
            {'type': 'scroll', 'selector': 'body', 'metric': 'scroll-delay'}
        ]
        
        results = []
        
        for interaction in interactions:
            elements = self.driver.find_elements(By.CSS_SELECTOR, interaction['selector'])
            if elements:
                element = elements[0]
                
                # 测量交互延迟
                delay = self._measure_interaction_delay(element, interaction['type'])
                
                results.append({
                    'interaction': interaction['type'],
                    'delay': delay,
                    'acceptable': delay < 100  # 100ms是可接受的交互延迟
                })
        
        return results
    
    def _measure_interaction_delay(self, element, interaction_type):
        """测量交互延迟"""
        script = """
        const element = arguments[0];
        const interactionType = arguments[1];
        
        return new Promise(resolve => {
            let startTime;
            let responded = false;
            
            // 设置响应检测
            const responseHandler = () => {
                if (!responded) {
                    responded = true;
                    const delay = performance.now() - startTime;
                    resolve(delay);
                }
            };
            
            // 监听可能的响应
            element.addEventListener('click', responseHandler);
            element.addEventListener('input', responseHandler);
            element.addEventListener('focus', responseHandler);
            document.addEventListener('scroll', responseHandler);
            
            // 记录开始时间并触发交互
            startTime = performance.now();
            
            if (interactionType === 'click') {
                element.click();
            } else if (interactionType === 'input') {
                element.focus();
                element.value = 'test';
                element.dispatchEvent(new Event('input'));
            } else if (interactionType === 'scroll') {
                window.scrollBy(0, 100);
            }
            
            // 超时处理
            setTimeout(() => {
                if (!responded) {
                    resolve(-1);  // 表示无响应
                }
            }, 5000);
        });
        """
        
        return self.driver.execute_async_script(script, element, interaction_type)
    
    def generate_optimization_suggestions(self, test_results):
        """基于测试结果生成优化建议"""
        suggestions = []
        
        # 加载性能建议
        if test_results['loading_performance']['total_load_time'] > 10:
            suggestions.append({
                'category': '加载性能',
                'priority': '高',
                'suggestions': [
                    '减少关键资源大小',
                    '实施代码分割',
                    '使用资源提示（preload, prefetch）',
                    '优化图片（使用WebP、懒加载）'
                ]
            })
        
        # 运行时性能建议
        if test_results['runtime_performance']['total_blocking_time'] > 300:
            suggestions.append({
                'category': '运行时性能',
                'priority': '高',
                'suggestions': [
                    '将长任务分解为较小的块',
                    '使用Web Workers处理计算密集任务',
                    '延迟非关键JavaScript执行',
                    '减少DOM操作'
                ]
            })
        
        # 内存使用建议
        if test_results['memory_pressure']['memory_leak_risk'] == 'high':
            suggestions.append({
                'category': '内存管理',
                'priority': '中',
                'suggestions': [
                    '清理事件监听器',
                    '避免意外的全局变量',
                    '及时释放大对象引用',
                    '使用虚拟滚动处理长列表'
                ]
            })
        
        return suggestions
```

这个解决方案包含了：
1. CPU和网络节流模拟
2. 加载性能详细指标
3. 运行时性能监控
4. 内存使用分析
5. 交互响应性测试
6. 具体的优化建议
</details>

### 进一步研究

- 移动端测试的未来：如何应对可折叠屏幕、多屏设备等新形态？
- 跨平台测试框架的统一：能否创建真正的"一次编写，处处测试"的框架？
- AI在移动测试中的应用：如何利用机器学习改进移动端的视觉测试？
- 5G对移动测试的影响：超低延迟如何改变测试策略？

## 7.5 工具：Selenium、Playwright、Cypress

现代浏览器自动化测试工具已经从简单的脚本记录器发展成为功能强大的测试框架。本节将深入探讨三个主流工具的架构、特点和最佳实践。

### 7.5.1 Selenium：经典之选

Selenium 作为最早的浏览器自动化工具之一，建立了许多至今仍在使用的核心概念。

**架构特点**：
- **WebDriver协议**：基于W3C标准的浏览器控制协议
- **客户端-服务器架构**：测试代码通过HTTP与浏览器驱动通信
- **多语言支持**：Java、Python、JavaScript、C#等
- **分布式测试**：Selenium Grid支持并行和跨浏览器测试

**核心概念**：
1. **定位策略**：ID、类名、标签名、CSS选择器、XPath
2. **等待机制**：显式等待、隐式等待、流畅等待
3. **动作链**：复杂用户交互的模拟
4. **JavaScript执行**：直接在浏览器中执行脚本

**优势与局限**：
- ✓ 成熟稳定，社区庞大
- ✓ 支持所有主流浏览器
- ✓ 适合大型企业级应用
- ✗ 相对较慢的执行速度
- ✗ 异步处理较为复杂
- ✗ 需要额外的驱动程序管理

### 7.5.2 Playwright：现代化方案

Playwright 由前Puppeteer团队开发，代表了浏览器自动化的新一代思想。

**创新特性**：
1. **自动等待**：智能等待元素就绪，减少显式等待
2. **网络拦截**：可以模拟、修改或阻止网络请求
3. **多浏览器上下文**：在单个测试中模拟多用户场景
4. **追踪和调试**：内置的追踪查看器和调试工具
5. **代码生成**：通过录制自动生成测试代码

**架构优势**：
- **统一API**：相同的API操作Chrome、Firefox、Safari
- **无头优先**：设计时就考虑了CI/CD环境
- **并行执行**：原生支持并行测试
- **跨浏览器截图**：像素级完美的截图比较

**高级功能**：
```
测试上下文隔离：
- 每个测试独立的浏览器状态
- 自动清理cookies和本地存储
- 并行测试互不干扰

网络控制能力：
- 模拟离线状态
- 修改请求响应
- 记录HAR文件
- 模拟不同网络速度
```

### 7.5.3 Cypress：开发者友好

Cypress 采用了完全不同的架构方法，将测试运行在浏览器内部。

**独特架构**：
- **浏览器内运行**：测试代码和应用代码在同一运行环境
- **时间旅行**：可以查看测试每一步的DOM快照
- **自动重试**：智能重试机制减少测试不稳定性
- **实时重载**：代码修改后自动重新运行测试

**开发体验优化**：
1. **交互式测试运行器**：可视化调试界面
2. **详细错误信息**：精确定位失败原因
3. **网络存根**：易于模拟API响应
4. **自定义命令**：扩展测试DSL

**适用场景**：
- 前端为主的应用测试
- 需要快速反馈的开发流程
- 单页应用（SPA）测试
- API和UI的集成测试

**局限性**：
- 仅支持Chrome系列浏览器
- 不支持多标签页测试
- 跨域限制（虽然有解决方案）
- 不适合需要多浏览器支持的场景

### 7.5.4 工具选择决策树

选择合适的工具需要考虑多个因素：

```
决策因素权重：
1. 浏览器覆盖需求（25%）
   - 需要Safari/移动浏览器 → Playwright/Selenium
   - 仅Chrome即可 → Cypress

2. 团队技术栈（20%）
   - JavaScript为主 → Cypress/Playwright
   - 多语言环境 → Selenium

3. 测试类型（20%）
   - E2E为主 → Cypress
   - 跨浏览器兼容性 → Playwright/Selenium

4. 性能要求（15%）
   - 速度优先 → Cypress
   - 稳定性优先 → Selenium

5. 维护成本（20%）
   - 低维护需求 → Playwright（自动等待）
   - 已有Selenium基础 → 继续Selenium
```

### 7.5.5 混合策略

实践中，许多团队采用混合策略：

1. **分层使用**：
   - Cypress用于开发阶段的快速反馈
   - Playwright用于CI/CD的跨浏览器测试
   - Selenium用于特定的企业级需求

2. **迁移路径**：
   - 保留关键Selenium测试
   - 新测试使用Playwright/Cypress
   - 逐步迁移旧测试

3. **工具互补**：
   - Cypress处理核心用户流程
   - Playwright处理跨浏览器场景
   - Selenium Grid处理大规模并行测试

### 练习 7.5

1. 设计一个测试场景，分别说明在什么情况下Selenium、Playwright和Cypress各自是最佳选择。

<details>
<summary>参考答案</summary>

三种工具的最佳场景：

**Selenium最佳场景**：
- 大型企业遗留系统，已有大量Selenium测试
- 需要支持IE11等老旧浏览器
- 团队使用Java/C#为主要语言
- 需要与企业测试管理工具集成
- 使用Selenium Grid进行大规模分布式测试

**Playwright最佳场景**：
- 新项目需要完整的跨浏览器测试
- 需要测试移动浏览器（iOS Safari）
- 复杂的网络模拟需求（API mocking）
- 需要并行测试提高效率
- 团队重视现代化工具和最佳实践

**Cypress最佳场景**：
- 前端团队主导的项目
- React/Vue/Angular单页应用
- 开发过程中需要即时反馈
- 主要用户使用Chrome/Edge
- 重视开发体验和调试效率
</details>

2. 如何设计一个抽象层，使得测试用例可以在不同的自动化工具间切换？

<details>
<summary>参考答案</summary>

可移植测试抽象层设计：

1. **Page Object抽象**：
```
interface LoginPage {
    enterUsername(username: string): Promise<void>
    enterPassword(password: string): Promise<void>
    submit(): Promise<void>
    getErrorMessage(): Promise<string>
}
```

2. **驱动适配器模式**：
```
interface WebDriver {
    navigate(url: string): Promise<void>
    findElement(selector: string): Promise<Element>
    wait(condition: () => boolean, timeout: number): Promise<void>
    takeScreenshot(): Promise<Buffer>
}
```

3. **工具特定实现**：
- SeleniumDriver implements WebDriver
- PlaywrightDriver implements WebDriver
- CypressDriver implements WebDriver

4. **配置驱动的工厂**：
```
function createDriver(type: 'selenium' | 'playwright' | 'cypress'): WebDriver {
    switch(type) {
        case 'selenium': return new SeleniumDriver()
        case 'playwright': return new PlaywrightDriver()
        case 'cypress': return new CypressDriver()
    }
}
```

5. **统一的测试DSL**：
- 使用链式API风格
- 统一的等待策略
- 通用的断言库
- 标准化的错误处理

这种设计允许在工具间切换，但要注意会失去各工具的特定优势。
</details>

### 进一步研究

- WebDriver BiDi协议：下一代浏览器自动化协议如何改变测试格局？
- 浏览器自动化检测：网站如何检测自动化工具，测试工具如何应对？
- 云端测试执行：如何优化大规模云端浏览器测试的成本和性能？
- AI辅助选择器：机器学习如何帮助生成更稳定的元素定位器？
- 测试录制的未来：如何让录制的测试更智能、更可维护？