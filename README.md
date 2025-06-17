# dependent-pattern-matching

依赖模式匹配和 Indexed Inductive Types 的最简单实现, 简单起见, 不考虑 elaboration. 对项的检查的部分高度参考 elaboration-zoo.
包含 elaboration 和终止检查的项目可以看 [ShiTT](https://github.com/KonjacSource/ShiTT).

阅读之前, 读者需要了解以下内容,
- 基本的依值类型实现 (双向类型检查)
- 了解 de Bruijn Index 和 Level, 以及基于此的求值
- 基本 Haskell 语法
- 对依赖模式匹配有基本的直觉 (或者你熟悉 GADT 也行)

阅读顺序:
- Syntax [Done]
  * 基本语法, 项的定义
- Definition [Done]
  * 类型, 函数定义的语法
- Context [Done]
  * 各种语境相关定义与工具
- Evaluation [Done]
  * 支持模式匹配的求值器, 基于 NBE.
- TypeChecker [Done]
  * 项的双向类型检查, 没写 elaborator
- FunctionChecker [TODO]
  * 检查函数 [Done]
  * 模式完全性检查 [TODO]

- Printer [Done]
- Parser [TODO]

有一篇写的很烂的[文章](design_proof_assistant_net.pdf).