def shll1 : instruction :=
  definst "shll" $ do
    pattern fun cl (v_2820 : reg (bv 32)) => do
      v_4662 <- getRegister rcx;
      v_4664 <- eval (bv_and (extract v_4662 56 64) (expression.bv_nat 8 31));
      v_4665 <- eval (eq v_4664 (expression.bv_nat 8 0));
      v_4666 <- eval (notBool_ v_4665);
      v_4667 <- getRegister v_2820;
      v_4671 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4667) (concat (expression.bv_nat 25 0) v_4664)) 0 33);
      v_4672 <- eval (extract v_4671 1 33);
      v_4675 <- getRegister zf;
      v_4679 <- eval (isBitSet v_4671 1);
      v_4681 <- getRegister sf;
      v_4688 <- getRegister pf;
      v_4692 <- eval (eq v_4664 (expression.bv_nat 8 1));
      v_4693 <- eval (uge v_4664 (expression.bv_nat 8 32));
      v_4698 <- getRegister cf;
      v_4703 <- eval (bit_or (bit_and v_4693 undef) (bit_and (notBool_ v_4693) (bit_or (bit_and v_4666 (isBitSet v_4671 0)) (bit_and v_4665 (eq v_4698 (expression.bv_nat 1 1))))));
      v_4708 <- eval (bit_and v_4666 undef);
      v_4709 <- getRegister of;
      v_4715 <- getRegister af;
      setRegister (lhs.of_reg v_2820) v_4672;
      setRegister af (bit_or v_4708 (bit_and v_4665 (eq v_4715 (expression.bv_nat 1 1))));
      setRegister cf v_4703;
      setRegister of (bit_or (bit_and v_4692 (notBool_ (eq v_4703 v_4679))) (bit_and (notBool_ v_4692) (bit_or v_4708 (bit_and v_4665 (eq v_4709 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4666 (parityFlag (extract v_4671 25 33))) (bit_and v_4665 (eq v_4688 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4666 v_4679) (bit_and v_4665 (eq v_4681 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4666 (eq v_4672 (expression.bv_nat 32 0))) (bit_and v_4665 (eq v_4675 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2823 : imm int) (v_2825 : reg (bv 32)) => do
      v_4727 <- eval (bv_and (handleImmediateWithSignExtend v_2823 8 8) (expression.bv_nat 8 31));
      v_4728 <- eval (eq v_4727 (expression.bv_nat 8 0));
      v_4729 <- eval (notBool_ v_4728);
      v_4730 <- getRegister v_2825;
      v_4734 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4730) (concat (expression.bv_nat 25 0) v_4727)) 0 33);
      v_4735 <- eval (extract v_4734 1 33);
      v_4738 <- getRegister zf;
      v_4742 <- eval (isBitSet v_4734 1);
      v_4744 <- getRegister sf;
      v_4751 <- getRegister pf;
      v_4755 <- eval (eq v_4727 (expression.bv_nat 8 1));
      v_4756 <- eval (uge v_4727 (expression.bv_nat 8 32));
      v_4761 <- getRegister cf;
      v_4766 <- eval (bit_or (bit_and v_4756 undef) (bit_and (notBool_ v_4756) (bit_or (bit_and v_4729 (isBitSet v_4734 0)) (bit_and v_4728 (eq v_4761 (expression.bv_nat 1 1))))));
      v_4771 <- eval (bit_and v_4729 undef);
      v_4772 <- getRegister of;
      v_4778 <- getRegister af;
      setRegister (lhs.of_reg v_2825) v_4735;
      setRegister af (bit_or v_4771 (bit_and v_4728 (eq v_4778 (expression.bv_nat 1 1))));
      setRegister cf v_4766;
      setRegister of (bit_or (bit_and v_4755 (notBool_ (eq v_4766 v_4742))) (bit_and (notBool_ v_4755) (bit_or v_4771 (bit_and v_4728 (eq v_4772 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4729 (parityFlag (extract v_4734 25 33))) (bit_and v_4728 (eq v_4751 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4729 v_4742) (bit_and v_4728 (eq v_4744 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4729 (eq v_4735 (expression.bv_nat 32 0))) (bit_and v_4728 (eq v_4738 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun cl (v_2809 : Mem) => do
      v_9597 <- evaluateAddress v_2809;
      v_9598 <- load v_9597 4;
      v_9600 <- getRegister rcx;
      v_9602 <- eval (bv_and (extract v_9600 56 64) (expression.bv_nat 8 31));
      v_9605 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9598) (concat (expression.bv_nat 25 0) v_9602)) 0 33);
      v_9606 <- eval (extract v_9605 1 33);
      store v_9597 v_9606 4;
      v_9608 <- eval (eq v_9602 (expression.bv_nat 8 0));
      v_9609 <- eval (notBool_ v_9608);
      v_9612 <- getRegister zf;
      v_9616 <- eval (isBitSet v_9605 1);
      v_9618 <- getRegister sf;
      v_9625 <- getRegister pf;
      v_9629 <- eval (eq v_9602 (expression.bv_nat 8 1));
      v_9630 <- eval (uge v_9602 (expression.bv_nat 8 32));
      v_9635 <- getRegister cf;
      v_9640 <- eval (bit_or (bit_and v_9630 undef) (bit_and (notBool_ v_9630) (bit_or (bit_and v_9609 (isBitSet v_9605 0)) (bit_and v_9608 (eq v_9635 (expression.bv_nat 1 1))))));
      v_9645 <- eval (bit_and v_9609 undef);
      v_9646 <- getRegister of;
      v_9652 <- getRegister af;
      setRegister af (bit_or v_9645 (bit_and v_9608 (eq v_9652 (expression.bv_nat 1 1))));
      setRegister cf v_9640;
      setRegister of (bit_or (bit_and v_9629 (notBool_ (eq v_9640 v_9616))) (bit_and (notBool_ v_9629) (bit_or v_9645 (bit_and v_9608 (eq v_9646 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9609 (parityFlag (extract v_9605 25 33))) (bit_and v_9608 (eq v_9625 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9609 v_9616) (bit_and v_9608 (eq v_9618 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9609 (eq v_9606 (expression.bv_nat 32 0))) (bit_and v_9608 (eq v_9612 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2813 : imm int) (v_2812 : Mem) => do
      v_9662 <- evaluateAddress v_2812;
      v_9663 <- load v_9662 4;
      v_9666 <- eval (bv_and (handleImmediateWithSignExtend v_2813 8 8) (expression.bv_nat 8 31));
      v_9669 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9663) (concat (expression.bv_nat 25 0) v_9666)) 0 33);
      v_9670 <- eval (extract v_9669 1 33);
      store v_9662 v_9670 4;
      v_9672 <- eval (eq v_9666 (expression.bv_nat 8 0));
      v_9673 <- eval (notBool_ v_9672);
      v_9676 <- getRegister zf;
      v_9680 <- eval (isBitSet v_9669 1);
      v_9682 <- getRegister sf;
      v_9689 <- getRegister pf;
      v_9693 <- eval (eq v_9666 (expression.bv_nat 8 1));
      v_9694 <- eval (uge v_9666 (expression.bv_nat 8 32));
      v_9699 <- getRegister cf;
      v_9704 <- eval (bit_or (bit_and v_9694 undef) (bit_and (notBool_ v_9694) (bit_or (bit_and v_9673 (isBitSet v_9669 0)) (bit_and v_9672 (eq v_9699 (expression.bv_nat 1 1))))));
      v_9709 <- eval (bit_and v_9673 undef);
      v_9710 <- getRegister of;
      v_9716 <- getRegister af;
      setRegister af (bit_or v_9709 (bit_and v_9672 (eq v_9716 (expression.bv_nat 1 1))));
      setRegister cf v_9704;
      setRegister of (bit_or (bit_and v_9693 (notBool_ (eq v_9704 v_9680))) (bit_and (notBool_ v_9693) (bit_or v_9709 (bit_and v_9672 (eq v_9710 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9673 (parityFlag (extract v_9669 25 33))) (bit_and v_9672 (eq v_9689 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9673 v_9680) (bit_and v_9672 (eq v_9682 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9673 (eq v_9670 (expression.bv_nat 32 0))) (bit_and v_9672 (eq v_9676 (expression.bv_nat 1 1))));
      pure ()
    pat_end
