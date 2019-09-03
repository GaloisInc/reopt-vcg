def cmpl1 : instruction :=
  definst "cmpl" $ do
    pattern fun (v_3367 : imm int) eax => do
      v_5485 <- eval (handleImmediateWithSignExtend v_3367 32 32);
      v_5489 <- getRegister rax;
      v_5492 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5485 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) (extract v_5489 32 64)));
      v_5497 <- eval (extract v_5492 1 2);
      v_5509 <- eval (eq (bv_xor (extract v_5485 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5509 (eq (extract v_5489 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_5509 (eq v_5497 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5492 25 33));
      setRegister af (bv_xor (bv_xor (extract v_5485 27 28) (extract v_5489 59 60)) (extract v_5492 28 29));
      setRegister zf (zeroFlag (extract v_5492 1 33));
      setRegister sf v_5497;
      setRegister cf (mux (notBool_ (eq (extract v_5492 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3380 : imm int) (v_3378 : reg (bv 32)) => do
      v_5532 <- eval (handleImmediateWithSignExtend v_3380 32 32);
      v_5536 <- getRegister v_3378;
      v_5538 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5532 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5536));
      v_5543 <- eval (extract v_5538 1 2);
      v_5554 <- eval (eq (bv_xor (extract v_5532 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5554 (eq (extract v_5536 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5554 (eq v_5543 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5538 25 33));
      setRegister af (bv_xor (extract (bv_xor v_5532 v_5536) 27 28) (extract v_5538 28 29));
      setRegister zf (zeroFlag (extract v_5538 1 33));
      setRegister sf v_5543;
      setRegister cf (mux (notBool_ (eq (extract v_5538 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3387 : reg (bv 32)) (v_3388 : reg (bv 32)) => do
      v_5573 <- getRegister v_3387;
      v_5577 <- getRegister v_3388;
      v_5579 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5573 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5577));
      v_5584 <- eval (extract v_5579 1 2);
      v_5595 <- eval (eq (bv_xor (extract v_5573 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5595 (eq (extract v_5577 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5595 (eq v_5584 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5579 25 33));
      setRegister af (bv_xor (extract (bv_xor v_5573 v_5577) 27 28) (extract v_5579 28 29));
      setRegister zf (zeroFlag (extract v_5579 1 33));
      setRegister sf v_5584;
      setRegister cf (mux (notBool_ (eq (extract v_5579 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3371 : imm int) (v_3370 : Mem) => do
      v_8804 <- eval (handleImmediateWithSignExtend v_3371 32 32);
      v_8808 <- evaluateAddress v_3370;
      v_8809 <- load v_8808 4;
      v_8811 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8804 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8809));
      v_8816 <- eval (extract v_8811 1 2);
      v_8827 <- eval (eq (bv_xor (extract v_8804 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8827 (eq (extract v_8809 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8827 (eq v_8816 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8811 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8804 v_8809) 27 28) (extract v_8811 28 29));
      setRegister zf (zeroFlag (extract v_8811 1 33));
      setRegister sf v_8816;
      setRegister cf (mux (notBool_ (eq (extract v_8811 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3375 : reg (bv 32)) (v_3374 : Mem) => do
      v_8842 <- getRegister v_3375;
      v_8846 <- evaluateAddress v_3374;
      v_8847 <- load v_8846 4;
      v_8849 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8842 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8847));
      v_8854 <- eval (extract v_8849 1 2);
      v_8865 <- eval (eq (bv_xor (extract v_8842 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8865 (eq (extract v_8847 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8865 (eq v_8854 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8849 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8842 v_8847) 27 28) (extract v_8849 28 29));
      setRegister zf (zeroFlag (extract v_8849 1 33));
      setRegister sf v_8854;
      setRegister cf (mux (notBool_ (eq (extract v_8849 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3383 : Mem) (v_3384 : reg (bv 32)) => do
      v_8880 <- evaluateAddress v_3383;
      v_8881 <- load v_8880 4;
      v_8885 <- getRegister v_3384;
      v_8887 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8881 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8885));
      v_8892 <- eval (extract v_8887 1 2);
      v_8903 <- eval (eq (bv_xor (extract v_8881 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8903 (eq (extract v_8885 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8903 (eq v_8892 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8887 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8881 v_8885) 27 28) (extract v_8887 28 29));
      setRegister zf (zeroFlag (extract v_8887 1 33));
      setRegister sf v_8892;
      setRegister cf (mux (notBool_ (eq (extract v_8887 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
