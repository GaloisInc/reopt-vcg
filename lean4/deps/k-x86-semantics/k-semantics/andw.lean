def andw1 : instruction :=
  definst "andw" $ do
    pattern fun (v_2876 : imm int) ax => do
      v_5772 <- getRegister rax;
      v_5774 <- eval (handleImmediateWithSignExtend v_2876 16 16);
      v_5778 <- eval (bv_and (extract v_5772 48 64) v_5774);
      setRegister rax (concat (extract v_5772 0 48) v_5778);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5772 63 64) (extract v_5774 15 16)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5772 62 63) (extract v_5774 14 15)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 61 62) (extract v_5774 13 14)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 60 61) (extract v_5774 12 13)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 59 60) (extract v_5774 11 12)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 58 59) (extract v_5774 10 11)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 57 58) (extract v_5774 9 10)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5772 56 57) (extract v_5774 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5778);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5772 48 49) (extract v_5774 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2889 : imm int) (v_2888 : reg (bv 16)) => do
      v_5843 <- getRegister v_2888;
      v_5845 <- eval (bv_and v_5843 (handleImmediateWithSignExtend v_2889 16 16));
      setRegister (lhs.of_reg v_2888) v_5845;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5845 8 16));
      setRegister zf (zeroFlag v_5845);
      setRegister af undef;
      setRegister sf (extract v_5845 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2897 : reg (bv 16)) (v_2898 : reg (bv 16)) => do
      v_5861 <- getRegister v_2898;
      v_5862 <- getRegister v_2897;
      v_5863 <- eval (bv_and v_5861 v_5862);
      setRegister (lhs.of_reg v_2898) v_5863;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5863 8 16));
      setRegister zf (zeroFlag v_5863);
      setRegister af undef;
      setRegister sf (extract v_5863 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2892 : Mem) (v_2893 : reg (bv 16)) => do
      v_9722 <- getRegister v_2893;
      v_9723 <- evaluateAddress v_2892;
      v_9724 <- load v_9723 2;
      v_9725 <- eval (bv_and v_9722 v_9724);
      setRegister (lhs.of_reg v_2893) v_9725;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9725 8 16));
      setRegister zf (zeroFlag v_9725);
      setRegister af undef;
      setRegister sf (extract v_9725 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2880 : imm int) (v_2879 : Mem) => do
      v_11303 <- evaluateAddress v_2879;
      v_11304 <- load v_11303 2;
      v_11306 <- eval (bv_and v_11304 (handleImmediateWithSignExtend v_2880 16 16));
      store v_11303 v_11306 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11306 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11306);
      setRegister sf (extract v_11306 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2884 : reg (bv 16)) (v_2883 : Mem) => do
      v_11318 <- evaluateAddress v_2883;
      v_11319 <- load v_11318 2;
      v_11320 <- getRegister v_2884;
      v_11321 <- eval (bv_and v_11319 v_11320);
      store v_11318 v_11321 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11321 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11321);
      setRegister sf (extract v_11321 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
