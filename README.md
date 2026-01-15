# Lean 4 Installation

You have two ways to work on this assignment:

1. **Install Lean on your own machine** (no containers)
2. **Use the provided Dev Container** (with Lean Pre-installed)

---

## Option 1: Install Lean on your own machine (no container)

### Install steps
1. **Install VS Code** (if you don’t already have it).
   https://code.visualstudio.com
  
2. **Install the Lean 4 extension**
   - Open VS Code → Extensions (left sidebar) → search **“Lean 4”** → install **Lean 4 (leanprover.lean4)**.
3. **Install Lean**
   - After installing the Lean 4 extension, VS Code will guide you through the remaining setup (it may prompt you to install tools like `elan` and download a Lean toolchain).
   - Official installer instructions: https://lean-lang.org/install

### Open the assignment
1. **Clone this repository**  
   Open a terminal and run:
   ```bash
   git clone https://github.com/AydenLamp/CSCI3382-MATH4313.git
   ```

2. **Open it in VS Code**
   ```bash
   code CSCI3381-MATH4313 
   ```

3. **Start coding**
   - Open `HomeworkExample/Basic.lean`.
   - Wait for the file to finish processing (the orange line in the left gutter should dissapear).
   - If the Lean Infoview panel is not open, click the **∀** icon and choose **Infoview: Toggle**.

> **Note:** The first time you open `Basic.lean`, you may see an error on the `import` line. If this happens, click **Restart File** in the Infoview.

---

## Option 2: Use the Dev Container (Lean preinstalled)

A **Dev Container** is like a lightweight VM that VS Code can connect to. This repo includes one that already has Lean (and dependencies) installed, so you don’t need to install Lean locally.

### Prerequisites
1. **Docker Desktop**
   - https://www.docker.com/products/docker-desktop  
   Docker runs the container. You don't need to understand exactly how it works; just install it and *make sure it is running before proceeding*.

2. **Visual Studio Code (VS Code)**
   - https://code.visualstudio.com

3. **Dev Containers extension for VS Code**
   - In VS Code → Extensions (on the left hand side) → search **“Dev Containers”** (by Microsoft) → install it.

### Getting started (Dev Container)
1. **Clone this repository**  
   Open a terminal and run:
   ```bash
   git clone https://github.com/AydenLamp/CSCI3382-MATH4313.git
   ```

2. **Open the folder in VS Code**
   ```bash
   code CSCI3382-MATH4313 
   ```
   Or use **File → Open Folder**.

3. **Reopen in Container**
   - When VS Code detects the `.devcontainer` folder, it should prompt:  
     > “Folder contains a Dev Container configuration file. Reopen folder to develop in a container?”
   - Click **Reopen in Container**.
   - If you miss the prompt: click the blue button in the bottom-left corner → **Reopen in Container**.
   - Wait 5-10 min for the container to build. You will not have to rebuild the container in the future, so re-entering the container will be much faster.

4. **Start coding**
   - Open `HomeworkExample/Basic.lean`.
   - Wait for the file to finish processing.
   - If the Lean Infoview panel is not open, click the **∀** icon and choose **Infoview: Toggle**.

> **Note:** The first time you open the container, you may see an error on the `import` statement in `Basic.lean`. To resolve this, click the blue **Restart File** button at the bottom of the Infoview panel.
