#!/bin/bash
# Build script for ITP 2026 paper

# Compile LaTeX
pdflatex -interaction=nonstopmode paper.tex
bibtex paper
pdflatex -interaction=nonstopmode paper.tex
pdflatex -interaction=nonstopmode paper.tex

echo "Build complete: paper.pdf"
