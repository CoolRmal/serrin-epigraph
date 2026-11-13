# 修正假设、势函数核验及两个目标的精确归约

本文件的初等引理给出证明。最后引用的分类定理有明确来源，但其证明不在本文件内；因此本文件不是用户要求的全部基础定理均展开的自包含证明。几何分类和定量平坦性证明分别在同目录的其他文件审查。这里不改变 `Basic.lean`、`Challenge.lean` 或两个主目标。

## 1. 假设和结论

环境维数与水平维数记作

$$n=m+1\ge2.$$

假设

$$g\in C^1(\mathbb R^m),\qquad
\Omega=\{(y,t):t>g(y)\},$$

$$u\in C^2(\Omega)\cap C^1_{\rm loc}(\overline\Omega),\qquad
-\Delta u=f(u),\qquad 0<u<1,$$

$$u=0,\quad\partial_\nu u=-\kappa\quad\hbox{在 }\partial\Omega,
\qquad\kappa>0,$$

$$f\in C^1_{\rm loc}([0,\infty)),\quad
f(s)-sf'(s)\ge0\ (s>0),\quad
f>0\text{ 在 }(0,1),\quad f(1)=0,\quad f'(1)<0.$$

保留目标中的质量假设

$$\liminf_{R\to\infty}\frac{\log(1+\int_{\Omega\cap B_R}u^2)}R=0.$$

两个目标分别额外假设

$$2\le n\le8,$$

或

$$n\ge9,\qquad
g(y)\ge-C(1+|y|)\quad\forall y,
\quad\text{或}\quad g(y)\le C(1+|y|)\quad\forall y,
\qquad C>0.$$

两者均须得到

$$\exists a\in\mathbb R^m,\ b\in\mathbb R,\ U:\mathbb R\to\mathbb R,
\quad g(y)=a\cdot y+b,$$

$$u(y,t)=U\!\left(\frac{t-a\cdot y-b}{\sqrt{1+|a|^2}}\right)
\quad(t>g(y)).$$

外法向导数的符号固定如上；使用范数、体积和正交变换时均为欧氏结构。

## 2. 反应项引理 R1：零点的非退化性

由连续性和内部正性，若零点值为负，则充分小的正参数处函数仍为负，矛盾。因此

$$f(0)\ge0.$$

若零点值为零，定义正半轴上的商函数。商法则和结构条件给出

$$q(s)=\frac{f(s)}s,\qquad
q'(s)=\frac{sf'(s)-f(s)}{s^2}\le0.$$

故对任意固定的内部点及其左侧正参数有

$$0<s<a<1\quad\Longrightarrow\quad
\frac{f(s)}s\ge\frac{f(a)}a>0.$$

令正参数趋于零；由于零点值为零，差商极限恰为右导数，得到

$$f'(0)\ge\frac{f(a)}a>0.$$

所以恰有以下两种允许情形：零点值严格正；或者零点值为零而零点导数严格正。此处没有另加假设。

## 3. 反应项引理 R2：不改变解值区间的延拓

记

$$\lambda=-f'(1)>0.$$

定义新的反应项，仅修改平衡点右侧：

$$\widetilde f(s)=
\begin{cases}
f(s),&0\le s\le1,\\
-\lambda(s-1)-(s-1)^2,&s\ge1.
\end{cases}$$

在拼接点，两侧函数值均为零，两侧一阶导数均为负的常数

$$\widetilde f(1)=0,\qquad
\widetilde f'(1-) = f'(1)=-\lambda=\widetilde f'(1+).$$

左右一阶导数连续至拼接点，因此延拓是一阶连续的。由于解值严格介于零与一，原方程逐点满足

$$-\Delta u=f(u)=\widetilde f(u).$$

Dirichlet、Neumann、域、单调性和质量条件均未改变。此操作用于应用依赖全非负轴反应项的外部定理；它不是把原目标中的反应项替换成更强的假设。

定义势函数

$$W(s)=\int_s^1\widetilde f(r)\,dr\qquad(s\ge0).$$

微积分基本定理给出

$$W'=-\widetilde f,\qquad W''=-\widetilde f',\qquad W\in C^2([0,\infty)).$$

当参数小于一时，积分在一个正长度区间上具有严格正的内部被积函数，所以势严格正。在一处势为零。在一的右侧直接计算得

$$W(1+t)=\frac\lambda2t^2+\frac13t^3\qquad(t\ge0).$$

因此势非负，唯一零点为一。其导数满足

$$W'(s)<0\quad(0<s<1),\qquad
W'(1+t)=\lambda t+t^2\ge t^2\quad(t>0).$$

后一不等式提供超线性增长指数二、系数一。

因为左侧二阶导数在一处等于正数，由连续性可取

$$\gamma\in(0,1),\qquad
W''(s)\ge\lambda/2\quad(\gamma\le s\le1).$$

右侧则有

$$W''(1+t)=\lambda+2t\ge\lambda\qquad(t\ge0).$$

合并得到整个区间上的统一严格凸性

$$W''\ge\lambda/2\quad\text{在 }[\gamma,\infty).$$

最后，R1 给出：若零点反应值为正，则势在零点的一阶导数非零；若反应值为零，则势的二阶导数为严格负数。这逐项验证 [Wang–Wei 的 W1–W5](https://arxiv.org/html/1502.04680#S1)；也逐项验证 [Beuvin–Farina 的 W1–W4](https://arxiv.org/html/2502.04812v2#S2)。两篇论文编号不同，不应把它们当作不同的额外假设。

## 4. 引理 R3：规范的一维剖面

此节独立构造剖面，不预先假定待证解已经一维。对内部参数定义

$$T(s)=\int_0^s\frac{dr}{\sqrt{2W(r)}}\qquad(0\le s<1).$$

势在任意闭子区间上有正的最小值，所以该积分有限、连续且严格递增，并在内部满足

$$T'(s)=\frac1{\sqrt{2W(s)}}>0.$$

选取上述左邻域，并用二阶导数连续性取有限正上界，使

$$0<c\le W''\le C\quad\text{在 }[\gamma,1].$$

从一处的函数值和一阶导数均为零出发，两次积分给出

$$W(s)=\int_s^1(r-s)W''(r)\,dr,
\qquad \frac c2(1-s)^2\le W(s)\le\frac C2(1-s)^2.$$

因此

$$T(s)-T(\gamma)\ge\frac1{\sqrt C}
\log\frac{1-\gamma}{1-s}\longrightarrow\infty.$$

故该严格递增函数把半开区间双射到非负半轴。取其反函数，记作规范剖面。逆函数求导给出

$$U(0)=0,\quad 0<U(t)<1\ (t>0),\quad
U'(t)=\sqrt{2W(U(t))}>0.$$

再求导即得

$$U''(t)=W'(U(t))=-f(U(t)).$$

在零点取右极限得到

$$U'(0)=\sqrt{2W(0)}.$$

反函数的满射性给出无穷远极限为一。更精确地，在剖面达到上述左邻域以后，令缺口为一减剖面；它满足

$$-\sqrt C(1-U)\le(1-U)'\le-\sqrt c(1-U).$$

积分这两个微分不等式得到指数上下界。界面能量有限，并且换元给出

$$\sigma=\int_0^\infty\left(\frac12U'(t)^2+W(U(t))\right)dt
=\int_0^1\sqrt{2W(s)}\,ds\in(0,\infty).$$

注意：构造出的剖面初始斜率，并不单凭本节就等于原解的 Neumann 常数。该等式要由原解的边界能量证明或最终一维性得到，禁止循环使用。

## 5. 引理 R4：从几何结论恢复 Lean 目标的坐标形式

假设已证明域是某个半空间，且解只依赖该半空间的向内法向距离。写成

$$\Omega=\{x:\nu\cdot x>d\},\qquad |\nu|=1.$$

每条竖直直线与原上图域的交集都是一个非空、非全体的向上开半线。若法向量竖直分量为零，半空间在固定水平点的截面只可能为空或整条直线，矛盾。若该分量为负，截面是向下半线，也矛盾。因此

$$\nu_n>0.$$

解半空间不等式得

$$t>\frac{d-\nu'\cdot y}{\nu_n}.$$

两个向上开半线相等必有相同端点，所以

$$g(y)=a\cdot y+b,\qquad
a=-\frac{\nu'}{\nu_n},\quad b=\frac d{\nu_n}.$$

由单位长度和正竖直分量，

$$1+|a|^2=\nu_n^{-2},\qquad
\nu\cdot(y,t)-d
=\frac{t-a\cdot y-b}{\sqrt{1+|a|^2}}.$$

这就是目标要求的坐标表达。原剖面只需定义在非负半轴；在负半轴任意延拓，例如取零，即得到 Lean 中全实轴上的函数，且不影响域内等式。

## 6. 两个结论的文献归约及其证明边界

第一主定理已经在本仓库证明严格竖直单调性。将 R2 的延拓代入 [Beuvin–Farina 定理 2.1](https://arxiv.org/html/2502.04812v2#S2.Thmtheorem2.1)，其定义域和解的正则性与第 1 节一致；低维分支不要求额外图形界，高维分支要求的恰是第 1 节两个单侧界之一。因此它分别给出两个目标的半空间及一维性；R4 完成坐标转换。

这是对一个已发表证明框架的精确归约，说明修正后的目标不需要额外猜测反应项条件。**它没有在本仓库展开定理 2.1 所用的极小边界正则性、锥分类和定量平坦性定理，因此不能算作用户要求的全部引理都写出证明的最终交付。** 也不能把该外部定理在 Lean 中声明为公理来关闭两个主目标。

低维单独调用 Wang–Wei 定理 1.4 时，还应核验其“光滑域”表述与这里的一阶边界之间的正则性提升；Beuvin–Farina 的定理明确以一阶边界表述，因此上述统一归约没有略去这个假设检查。它的内部证明使用的正则性提升仍是完整展开版的任务。
