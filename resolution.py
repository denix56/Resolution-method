import sys

from pyprover import *
from PyQt5 import QtGui, QtCore

from PyQt5.QtWidgets import QLabel, QMainWindow, QApplication, QPushButton, QLineEdit, QPlainTextEdit
from PyQt5.QtCore import pyqtSlot

class App(QMainWindow):
 
    def __init__(self):
        super().__init__()
        self.title = 'Resolution theorem prover'
        self.left = 300
        self.top = 300
        self.width = 600
        self.height = 600
        self.initUI()
 
    def initUI(self):
        self.setWindowTitle(self.title)
        self.setGeometry(self.left, self.top, self.width, self.height)

        # Create textboxGivens
        self.textboxExpr = QLineEdit(self)
        self.textboxExpr.move(20, 20)
        self.textboxExpr.resize(300, 30)

        font = self.textboxExpr.font()
        font.setPointSize(10)
        self.textboxExpr.setFont(font)

        # Create textboxConclusion
        self.textboxConc = QLineEdit(self)
        self.textboxConc.move(330, 20)
        self.textboxConc.resize(50, 30)
        font = self.textboxConc.font()
        font.setPointSize(10)
        self.textboxConc.setFont(font)

        self.verboseText = QPlainTextEdit(self)
        self.verboseText.setReadOnly(True)
        self.verboseText.move(20, 60)
        self.verboseText.resize(550, 500)
        font = self.verboseText.font()
        font.setPointSize(12)
        self.verboseText.setFont(font)


        # Create a button in the window
        self.button = QPushButton('Resolute', self)
        self.button.move(400, 20)
 
        # connect button to function on_click
        self.button.clicked.connect(self.on_click)
        self.show()

    def printExpr(self, idx : int, expr, val_to_names : dict, parents = ()):
        self.verboseText.appendPlainText(str(idx) + ') ' + ' ∨ '.join(
            ('¬' if x < 0 else '') + str(val_to_names[abs(x)]) for x in expr) +
                                         ('\t resolvent of ' + str(parents) if parents else '') + '\n')
    def printExprStr(self, idx : int, expr_str : str, parents = ()):
        self.verboseText.appendPlainText(str(idx) + ') ' + expr_str +
                                         ('\t resolvent of ' + str(parents) if parents else '') + '\n')
 
    @pyqtSlot()
    def on_click(self):
        if self.textboxConc.text() is '' or self.textboxExpr.text() is '':
            return
        try:
            text = '(' + (self.textboxExpr.text() + ', ~' + self.textboxConc.text())\
                .replace(' ', '').replace(',', ')/\\(') + ')'
            givens = expr( text )
            concl = expr( self.textboxConc.text() )

            simplified_str = str( simplify(givens))

            self.verboseText.setPlainText('Expression: ' + simplified_str + '\n')

            simplified_str = simplified_str.split('∧')

            expressions = []
            simplified_str = [simplified_str[-1]] + simplified_str[:-1]
            liters = []
            expr_parts = []
            b = '() '
            for let in simplified_str:
                for s in b:
                    let = let.replace(s, '')
                if len(let) == 1 or len(let) == 2 and let[0] == '¬':
                    liters.append(let)
                else:
                    expr_parts.append(let)
            simplified_str = liters + expr_parts

            dict_letters = dict()
            dict_values = dict()
            created_resolvents = set()
            for ex in simplified_str:
                cur = ex.split('∨')
                cur_exp = set()
                for symb in cur:
                    letter = symb.replace('¬', '')

                    if letter not in dict_letters:
                        dict_letters[letter] = len(dict_letters) + 1
                        dict_values[dict_letters[letter]] = letter
                    cur_exp.add(dict_letters[letter] * (-1 if '¬' in symb else 1))
                expressions.append(cur_exp)
                self.printExpr(len(expressions), cur_exp, dict_values)

            i = 0
            result = False

            while (not result) and (i < len(expressions) - 1):
                for j in range(i + 1, len(expressions)):
                    if not (expressions[j] <= expressions[i]):
                        tmp = expressions[i].union(expressions[j])
                        new_exp = set()
                        has_conc_pair = False
                        for l in tmp:
                            if -l in tmp:
                                has_conc_pair = True
                            else:
                                new_exp.add(l)

                        if has_conc_pair and new_exp not in expressions:
                            if len(new_exp) == 0:
                                result = True
                                self.printExprStr(len(expressions) + 1, '▯', (i + 1, j + 1))
                                break
                            else:
                                expressions.append(new_exp)
                                self.printExpr(len(expressions), new_exp, dict_values, (i + 1, j + 1))
                i += 1
            if result:
                self.verboseText.appendPlainText('Theorem proved.')
            else:
                self.verboseText.appendPlainText('Theorem was not proved.')
        except:
            self.verboseText.appendPlainText('Incorrect expression.')



if __name__ == '__main__':
    app = QApplication(sys.argv)
    ex = App()
    sys.exit(app.exec_())
