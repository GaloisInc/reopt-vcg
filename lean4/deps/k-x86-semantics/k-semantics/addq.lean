def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (v_2618 : imm int) (v_2620 : reg (bv 64)) => do
      v_4808 <- eval (handleImmediateWithSignExtend v_2618 32 32);
      v_4810 <- eval (mi 64 (svalueMInt v_4808));
      v_4812 <- getRegister v_2620;
      v_4814 <- eval (add (concat (expression.bv_nat 1 0) v_4810) (concat (expression.bv_nat 1 0) v_4812));
      v_4816 <- eval (extract v_4814 1 2);
      v_4822 <- eval (extract v_4814 1 65);
      v_4827 <- eval (eq (extract v_4810 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2620) v_4822;
      setRegister of (mux (bit_and (eq v_4827 (eq (extract v_4812 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4827 (eq v_4816 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4814 57 65));
      setRegister zf (zeroFlag v_4822);
      setRegister af (bv_xor (bv_xor (extract v_4808 27 28) (extract v_4812 59 60)) (extract v_4814 60 61));
      setRegister sf v_4816;
      setRegister cf (extract v_4814 0 1);
      pure ()
    pat_end;
    pattern fun (v_2628 : reg (bv 64)) (v_2629 : reg (bv 64)) => do
      v_4847 <- getRegister v_2628;
      v_4849 <- getRegister v_2629;
      v_4851 <- eval (add (concat (expression.bv_nat 1 0) v_4847) (concat (expression.bv_nat 1 0) v_4849));
      v_4853 <- eval (extract v_4851 1 2);
      v_4858 <- eval (extract v_4851 1 65);
      v_4863 <- eval (eq (extract v_4847 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2629) v_4858;
      setRegister of (mux (bit_and (eq v_4863 (eq (extract v_4849 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4863 (eq v_4853 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4851 57 65));
      setRegister zf (zeroFlag v_4858);
      setRegister af (bv_xor (extract (bv_xor v_4847 v_4849) 59 60) (extract v_4851 60 61));
      setRegister sf v_4853;
      setRegister cf (extract v_4851 0 1);
      pure ()
    pat_end;
    pattern fun (v_2623 : Mem) (v_2624 : reg (bv 64)) => do
      v_9151 <- evaluateAddress v_2623;
      v_9152 <- load v_9151 8;
      v_9154 <- getRegister v_2624;
      v_9156 <- eval (add (concat (expression.bv_nat 1 0) v_9152) (concat (expression.bv_nat 1 0) v_9154));
      v_9158 <- eval (extract v_9156 1 2);
      v_9163 <- eval (extract v_9156 1 65);
      v_9168 <- eval (eq (extract v_9152 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2624) v_9163;
      setRegister of (mux (bit_and (eq v_9168 (eq (extract v_9154 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9168 (eq v_9158 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9156 57 65));
      setRegister zf (zeroFlag v_9163);
      setRegister af (bv_xor (extract (bv_xor v_9152 v_9154) 59 60) (extract v_9156 60 61));
      setRegister sf v_9158;
      setRegister cf (extract v_9156 0 1);
      pure ()
    pat_end;
    pattern fun (v_2611 : imm int) (v_2610 : Mem) => do
      v_10734 <- evaluateAddress v_2610;
      v_10735 <- eval (handleImmediateWithSignExtend v_2611 32 32);
      v_10737 <- eval (mi 64 (svalueMInt v_10735));
      v_10739 <- load v_10734 8;
      v_10741 <- eval (add (concat (expression.bv_nat 1 0) v_10737) (concat (expression.bv_nat 1 0) v_10739));
      v_10742 <- eval (extract v_10741 1 65);
      store v_10734 v_10742 8;
      v_10745 <- eval (extract v_10741 1 2);
      v_10755 <- eval (eq (extract v_10737 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10755 (eq (extract v_10739 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10755 (eq v_10745 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10741 57 65));
      setRegister af (bv_xor (bv_xor (extract v_10735 27 28) (extract v_10739 59 60)) (extract v_10741 60 61));
      setRegister zf (zeroFlag v_10742);
      setRegister sf v_10745;
      setRegister cf (extract v_10741 0 1);
      pure ()
    pat_end;
    pattern fun (v_2615 : reg (bv 64)) (v_2614 : Mem) => do
      v_10770 <- evaluateAddress v_2614;
      v_10771 <- getRegister v_2615;
      v_10773 <- load v_10770 8;
      v_10775 <- eval (add (concat (expression.bv_nat 1 0) v_10771) (concat (expression.bv_nat 1 0) v_10773));
      v_10776 <- eval (extract v_10775 1 65);
      store v_10770 v_10776 8;
      v_10779 <- eval (extract v_10775 1 2);
      v_10788 <- eval (eq (extract v_10771 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10788 (eq (extract v_10773 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10788 (eq v_10779 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10775 57 65));
      setRegister af (bv_xor (extract (bv_xor v_10771 v_10773) 59 60) (extract v_10775 60 61));
      setRegister zf (zeroFlag v_10776);
      setRegister sf v_10779;
      setRegister cf (extract v_10775 0 1);
      pure ()
    pat_end
