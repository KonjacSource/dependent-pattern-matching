# dependent-pattern-matching

依赖模式匹配的最简单示例, 简单起见, 不考虑 elaboration.
阅读之前, 读者需要了解以下内容,
- 基本的依值类型实现 (双向类型检查)
- 了解 de Bruijn Index 和 Level, 以及基于此的求值
- 基本 Haskell 语法


阅读顺序, 同时也是依赖顺序:
- Syntax [Done]
  * 基本语法, 项的定义
- Definition [Done]
  * 类型, 函数定义的语法
- Context [Done]
  * 各种语境相关定义与工具
- Evaluation [TODO]
  * 求值器, 基于 NBE
- TypeChecker [TODO]
  * 项的双向类型检查, 没写 elaborator
- FunctionChecker [TODO]
  * 检查函数, 这是本项目的关键
- Parser [TODO]
  * 这个 Parser 写的很烂, 它在解析的同时进行类型检查

有一篇写的很烂的文章在 [TODO].