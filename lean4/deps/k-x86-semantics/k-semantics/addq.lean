def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (v_2633 : imm int) (v_2632 : reg (bv 64)) => do
      v_4891 <- eval (handleImmediateWithSignExtend v_2633 32 32);
      v_4892 <- eval (leanSignExtend v_4891 64);
      v_4894 <- getRegister v_2632;
      v_4896 <- eval (add (concat (expression.bv_nat 1 0) v_4892) (concat (expression.bv_nat 1 0) v_4894));
      v_4898 <- eval (extract v_4896 1 2);
      v_4904 <- eval (extract v_4896 1 65);
      v_4909 <- eval (eq (extract v_4892 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2632) v_4904;
      setRegister of (mux (bit_and (eq v_4909 (eq (extract v_4894 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4909 (eq v_4898 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4896 57 65));
      setRegister zf (zeroFlag v_4904);
      setRegister af (bv_xor (bv_xor (extract v_4891 27 28) (extract v_4894 59 60)) (extract v_4896 60 61));
      setRegister sf v_4898;
      setRegister cf (extract v_4896 0 1);
      pure ()
    pat_end;
    pattern fun (v_2641 : reg (bv 64)) (v_2642 : reg (bv 64)) => do
      v_4929 <- getRegister v_2641;
      v_4931 <- getRegister v_2642;
      v_4933 <- eval (add (concat (expression.bv_nat 1 0) v_4929) (concat (expression.bv_nat 1 0) v_4931));
      v_4935 <- eval (extract v_4933 1 2);
      v_4940 <- eval (extract v_4933 1 65);
      v_4945 <- eval (eq (extract v_4929 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2642) v_4940;
      setRegister of (mux (bit_and (eq v_4945 (eq (extract v_4931 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4945 (eq v_4935 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4933 57 65));
      setRegister zf (zeroFlag v_4940);
      setRegister af (bv_xor (extract (bv_xor v_4929 v_4931) 59 60) (extract v_4933 60 61));
      setRegister sf v_4935;
      setRegister cf (extract v_4933 0 1);
      pure ()
    pat_end;
    pattern fun (v_2636 : Mem) (v_2637 : reg (bv 64)) => do
      v_9363 <- evaluateAddress v_2636;
      v_9364 <- load v_9363 8;
      v_9366 <- getRegister v_2637;
      v_9368 <- eval (add (concat (expression.bv_nat 1 0) v_9364) (concat (expression.bv_nat 1 0) v_9366));
      v_9370 <- eval (extract v_9368 1 2);
      v_9371 <- eval (extract v_9368 1 65);
      v_9380 <- eval (eq (extract v_9364 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2637) v_9371;
      setRegister of (mux (bit_and (eq v_9380 (eq (extract v_9366 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9380 (eq v_9370 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9368 57 65));
      setRegister af (bv_xor (extract (bv_xor v_9364 v_9366) 59 60) (extract v_9368 60 61));
      setRegister zf (zeroFlag v_9371);
      setRegister sf v_9370;
      setRegister cf (extract v_9368 0 1);
      pure ()
    pat_end;
    pattern fun (v_2624 : imm int) (v_2623 : Mem) => do
      v_11019 <- evaluateAddress v_2623;
      v_11020 <- eval (handleImmediateWithSignExtend v_2624 32 32);
      v_11021 <- eval (leanSignExtend v_11020 64);
      v_11023 <- load v_11019 8;
      v_11025 <- eval (add (concat (expression.bv_nat 1 0) v_11021) (concat (expression.bv_nat 1 0) v_11023));
      v_11026 <- eval (extract v_11025 1 65);
      store v_11019 v_11026 8;
      v_11029 <- eval (extract v_11025 1 2);
      v_11039 <- eval (eq (extract v_11021 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_11039 (eq (extract v_11023 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_11039 (eq v_11029 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11025 57 65));
      setRegister af (bv_xor (bv_xor (extract v_11020 27 28) (extract v_11023 59 60)) (extract v_11025 60 61));
      setRegister zf (zeroFlag v_11026);
      setRegister sf v_11029;
      setRegister cf (extract v_11025 0 1);
      pure ()
    pat_end;
    pattern fun (v_2628 : reg (bv 64)) (v_2627 : Mem) => do
      v_11054 <- evaluateAddress v_2627;
      v_11055 <- getRegister v_2628;
      v_11057 <- load v_11054 8;
      v_11059 <- eval (add (concat (expression.bv_nat 1 0) v_11055) (concat (expression.bv_nat 1 0) v_11057));
      v_11060 <- eval (extract v_11059 1 65);
      store v_11054 v_11060 8;
      v_11063 <- eval (extract v_11059 1 2);
      v_11072 <- eval (eq (extract v_11055 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_11072 (eq (extract v_11057 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_11072 (eq v_11063 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11059 57 65));
      setRegister af (bv_xor (extract (bv_xor v_11055 v_11057) 59 60) (extract v_11059 60 61));
      setRegister zf (zeroFlag v_11060);
      setRegister sf v_11063;
      setRegister cf (extract v_11059 0 1);
      pure ()
    pat_end
