# 关于使用AI

使用AI进行翻译务必**人工**进行这些检查
- 是否存在漏翻/多翻译的情况: 部分大模型会漏翻长句会整段话中的某些部分, 必须対每句话进行检查
- 翻译的一致性: 检查翻译结果中対某些名词的翻译是否一致，比如constructor 大部分情况会被翻译成 `构造器` 或 `构造函数`, lean的语境下应翻译成`构造子`
- 语句的通顺: AI有时会为了保证翻译的准确，翻译出的句子很难理解。

# Best Prcatise
- 无需采用思维链模型(如deepeek-R1, openai的O3,O4-mini)，思维链模型在翻译上并没有更好的效果
- 目前实验效果最好的模型是gpt-4.1，但是仍然存在部分格式不匹配等问题，需要人工介入。
- 一次喂给AI一整个文档，而不是单个句子，整篇文档有助于AI理解文档内容提高翻译质量
- 尽量采用单轮对话，如果有需要修改的就增加更多的说明在提示词上重新输入，而不是让AI在原输出上进行修改。

# 提示词

你是一个lean4专家, 対lean4的用户手册进行翻译
- 保持原代码格式, 原文不是markdown，所以不要修改任何符号
- 翻译应当尽可能的便于理解, 为了保证易于理解不必逐个单词翻译
- 不能遗漏句子
- 不能额外添加句子
- 遇到`{tech}[xxx]`，将其改成 `{tech key := "xxx"}[中文]` 的格式 , 一定要添加 `key := "xxx"`
- 遇到`{deftech}_xxx_` 时，修改为 `{deftech key := "xxx"}_中文_`, 一定要添加 `key := "xxx"`
- 如果原文中没有使用`{tech}`或`{deftech}`，则不要添加

- 以下单词按照表进行翻译
```
aad-hoc  特设（的）
alternative 选取（的）
anti-symmetric  反对称性
arithmetic  算术（的）
associative 结合律
binary operator 二元运算符
bisimulation  互拟
coalgebra 逆代数
codata type 逆数据类型
coinduction 逆归纳
commutative 交换律
composite type  复合类型
comprehen(sive|sion)  概括
confluence  合流性
construct 构造
context 语境
copattern 逆模式
data constructor  数据构造子
de Bruijn 【名字不翻译】
dependent pair  依值有序对
dependent record  依值记录体
dependent type  依值类型
distribute  分配律
elaborate/elaboration 繁释
evidence  证据
expression  表达式
family of type  类型族
fixity declaration  缀序声明
hole  洞
identity  幺元
idiom bracket 习语括号
implicit argument 隐式参数
interpreter 解释器
justification 依据
laziness  惰性
list comprehensive  列表推导
literal 字面量
mutual block  互递归块
operand 操作数
operator section  操作符段
parameteri(se|ze) 参数化
partial function  偏函数
pattern matching  模式匹配
prelude   前导库
primitive type  原语类型
qualifier 限定式
reasoning 推理
record  记录体
reflection  反射
reflexive 自反性
row polymorphism  行多态
scope 作用域
struct  结构体
symmetric 对称性
term  项
totality  完全性
total function  全函数
transitive  传递性
type checker  类型检查器
type constructor  类型构造器
type inference  类型推断
vector  向量
well-formed 良构的
well-typed  良型的
congruence  合同性
metavariables 元变量
heterogeneous 异质
heterogeneous addition  异质加法
IO actions  IO 操作
unification 归一
carrier set 载体集
coercion  强制转换
elaborator	繁释
choice node	备选节点
kind	类别
environment extensions	环境扩展
info trees	信息树
kernel	内核
auxiliary matching function	辅助匹配函数
pre-definition	预定义
well-founded recursion	良构递归
measure	度量
partial fixpoint	偏不动点
equational lemmas	等式引理
.olean file	`.olean` 文件
initialization	初始化
term	项
expression	表达式
well-typed	良型的
constructor	构造子
type constructor	类型构造子
recursor	递归子
defined constant	已定义常量
derivation	演绎
evidence	证据
definitional equality	定义等价
reduction	规约
bound variables	绑定变量
normal form	规范形式
η-equivalence	η-等价
proof irrelevance	证明无关性
universe	宇宙
function	函数
inductive type	归纳类型
axiom	公理
opaque constant	不透明常量
proposition	命题
context	上下文
impredicative	非直谓的
universe level	宇宙层级
subsingleton	子单元
extensionality	外延性
propositional extensionality	命题外延性
predicative	直谓性的
cumulative	累积性的
universe polymorphism	宇宙多态
universe parameter	宇宙参数
identity function	身份函数
section scope	作用域
universe lifting	宇宙提升
```