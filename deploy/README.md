<!--
# Deployment Infrastructure

TL;DR: push a tag of the form `vX.Y.Z` onto the commit that should be
released as the manual for that version, and the rest is automatic.

This directory contains the deployment infrastructure for the
reference manual. Deployment happens in GitHub Actions, in response to
certain tags being pushed. Because the latest version of the GH action
file will always be used, and we want to be able to mutate tags to
re-deploy old manual versions (e.g. to update CSS for consistent look
and feel while keeping content version-accurate, or add a "THIS IS
OBSOLETE" banner in a few years). Thus, the steps of the workflow that
might change are captured in scripts that are versioned along with the
code.

The files are:

* `prep.sh` is used to set up the build, installing OS-level
  dependencies and Elan.
  
* `build.sh` is used to build the executable that generates the
  manual.
  
* `generate.sh` actually generates release-ready HTML, saving it in
  `/html` in the root of this repository.
  
* `release.py` puts the generated HTML in the right place on the
  deployment branch.
-->

# 部署框架

简而言之：将形式为 `vX.Y.Z` 的标签推送到应该作为该版本手册发布的提交上，其余部分都是自动完成的。

此目录包含参考手册的部署框架。部署发生在 GitHub Actions 中，响应某些标签的推送。由于始终会使用最新版本的 GH action 文件，并且我们希望能够更改标签以重新部署旧的手册版本（例如，为了更新 CSS 以保持一致的外观并确保内容版本的准确性，或者在几年后添加“THIS IS OBSOLETE”横幅）。因此，工作流中可能会更改的步骤都被收集在与代码一起版本化的脚本中。

包括的文件有：

* `prep.sh` 用于设置构建环境，安装操作系统级依赖和 Elan。
  
* `build.sh` 用于构建生成手册的可执行文件。
  
* `generate.sh` 实际生成可发布的 HTML，并将其保存到本仓库根目录下的 `/html` 中。
  
* `release.py` 将生成的 HTML 放置到部署分支上的正确位置。
  
<!-- 
## Deployment Overview

The goal is to have versioned snapshots of the manual, with a structure like:

 * `https://lean-lang.org/doc/reference/latest/`- latest version
 * `https://lean-lang.org/doc/reference/4.19.0/` - manual for v4.19.0
 * `https://lean-lang.org/doc/reference/4.20.0/` - manual for v4.19.0
 
and so forth.  `https://lean-lang.org/doc/reference/` should redirect
to `latest`. It's important to be able to edit past deployments as well.

An orphan branch, called `deploy`, should at all times contain this
structure. With the three URLs above, the branch would contain three
directories:

 * `/4.20.0/` - built HTML served for 4.20.0 
 * `/4.19.0/` - built HTML served for 4.19.0 
 * `/latest` - symlink to `/4.20.0`

The `release.py` script is responsible for updating this structure. It
takes the generated HTML directory, the version number, and the
deployment branch name as arguments, and then does the following:
 1. It copies the HTML to the branch (deleting an existing directory
    first if needed).
 2. It updates the `latest` symlink to point at the most recent
    version, with all numbered releases being considered more recent
    than any nightly and real releases being more recent than their
    RCs.
 3. It commits the changes to the deployment branch, then switches
    back to the original branch.

After this, the GH Action for deployment pushes the edited deploy
branch. Another action is responsible for actually deploying the
contents of this branch when it's pushed.

## 
-->

## 部署概述

目标是拥有手册的版本快照，结构如下：

 * `https://lean-lang.org/doc/reference/latest/` - 最新版本
 * `https://lean-lang.org/doc/reference/4.19.0/` - v4.19.0 的手册
 * `https://lean-lang.org/doc/reference/4.20.0/` - v4.19.0 的手册
 
以此类推。`https://lean-lang.org/doc/reference/` 应该重定向到 `latest`。能够编辑过去的部署版本也很重要。

一个名为 `deploy` 的分支应始终包含这种结构。对于上述三个 URL，分支应包含三个目录：

 * `/4.20.0/` - 提供 4.20.0 的构建 HTML 
 * `/4.19.0/` - 提供 4.19.0 的构建 HTML 
 * `/latest` - 指向 `/4.20.0` 的符号链接

`release.py` 脚本负责更新此结构。它接受生成的 HTML 目录、版本号和部署分支名称作为参数，然后执行以下操作：
 1. 将 HTML 复制到分支（如有需要，先删除现有目录）。
 2. 更新 `latest` 符号链接，使其指向最新版本，所有编号释版本被视为比任何夜间版本更“新”，正式版本则比其 RC 更“新”。
 3. 提交对部署分支的更改，然后切换回原始分支。

之后，部署用的 GH Action 会推送已修改的 deploy 分支。另一个 action 会在这个分支被推送时实际部署其内容。
