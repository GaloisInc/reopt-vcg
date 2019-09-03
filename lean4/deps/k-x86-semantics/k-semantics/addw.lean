def addw1 : instruction :=
  definst "addw" $ do
    pattern fun (v_2672 : imm int) ax => do
      v_4998 <- eval (handleImmediateWithSignExtend v_2672 16 16);
      v_5000 <- getRegister rax;
      v_5003 <- eval (add (concat (expression.bv_nat 1 0) v_4998) (concat (expression.bv_nat 1 0) (extract v_5000 48 64)));
      v_5005 <- eval (extract v_5003 1 2);
      v_5011 <- eval (extract v_5003 1 17);
      v_5016 <- eval (eq (extract v_4998 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_5000 0 48) v_5011);
      setRegister of (mux (bit_and (eq v_5016 (eq (extract v_5000 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_5016 (eq v_5005 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5003 9 17));
      setRegister zf (zeroFlag v_5011);
      setRegister af (bv_xor (bv_xor (extract v_4998 11 12) (extract v_5000 59 60)) (extract v_5003 12 13));
      setRegister sf v_5005;
      setRegister cf (extract v_5003 0 1);
      pure ()
    pat_end;
    pattern fun (v_2684 : imm int) (v_2686 : reg (bv 16)) => do
      v_5042 <- eval (handleImmediateWithSignExtend v_2684 16 16);
      v_5044 <- getRegister v_2686;
      v_5046 <- eval (add (concat (expression.bv_nat 1 0) v_5042) (concat (expression.bv_nat 1 0) v_5044));
      v_5048 <- eval (extract v_5046 1 2);
      v_5049 <- eval (extract v_5046 1 17);
      v_5058 <- eval (eq (extract v_5042 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2686) v_5049;
      setRegister of (mux (bit_and (eq v_5058 (eq (extract v_5044 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5058 (eq v_5048 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5046 9 17));
      setRegister af (bv_xor (extract (bv_xor v_5042 v_5044) 11 12) (extract v_5046 12 13));
      setRegister zf (zeroFlag v_5049);
      setRegister sf v_5048;
      setRegister cf (extract v_5046 0 1);
      pure ()
    pat_end;
    pattern fun (v_2694 : reg (bv 16)) (v_2695 : reg (bv 16)) => do
      v_5078 <- getRegister v_2694;
      v_5080 <- getRegister v_2695;
      v_5082 <- eval (add (concat (expression.bv_nat 1 0) v_5078) (concat (expression.bv_nat 1 0) v_5080));
      v_5084 <- eval (extract v_5082 1 2);
      v_5085 <- eval (extract v_5082 1 17);
      v_5094 <- eval (eq (extract v_5078 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2695) v_5085;
      setRegister of (mux (bit_and (eq v_5094 (eq (extract v_5080 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5094 (eq v_5084 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5082 9 17));
      setRegister af (bv_xor (extract (bv_xor v_5078 v_5080) 11 12) (extract v_5082 12 13));
      setRegister zf (zeroFlag v_5085);
      setRegister sf v_5084;
      setRegister cf (extract v_5082 0 1);
      pure ()
    pat_end;
    pattern fun (v_2689 : Mem) (v_2690 : reg (bv 16)) => do
      v_9256 <- evaluateAddress v_2689;
      v_9257 <- load v_9256 2;
      v_9259 <- getRegister v_2690;
      v_9261 <- eval (add (concat (expression.bv_nat 1 0) v_9257) (concat (expression.bv_nat 1 0) v_9259));
      v_9263 <- eval (extract v_9261 1 2);
      v_9268 <- eval (extract v_9261 1 17);
      v_9273 <- eval (eq (extract v_9257 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2690) v_9268;
      setRegister of (mux (bit_and (eq v_9273 (eq (extract v_9259 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9273 (eq v_9263 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9261 9 17));
      setRegister zf (zeroFlag v_9268);
      setRegister af (bv_xor (extract (bv_xor v_9257 v_9259) 11 12) (extract v_9261 12 13));
      setRegister sf v_9263;
      setRegister cf (extract v_9261 0 1);
      pure ()
    pat_end;
    pattern fun (v_2677 : imm int) (v_2676 : Mem) => do
      v_10803 <- evaluateAddress v_2676;
      v_10804 <- eval (handleImmediateWithSignExtend v_2677 16 16);
      v_10806 <- load v_10803 2;
      v_10808 <- eval (add (concat (expression.bv_nat 1 0) v_10804) (concat (expression.bv_nat 1 0) v_10806));
      v_10809 <- eval (extract v_10808 1 17);
      store v_10803 v_10809 2;
      v_10812 <- eval (extract v_10808 1 2);
      v_10821 <- eval (eq (extract v_10804 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10821 (eq (extract v_10806 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10821 (eq v_10812 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10808 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10804 v_10806) 11 12) (extract v_10808 12 13));
      setRegister zf (zeroFlag v_10809);
      setRegister sf v_10812;
      setRegister cf (extract v_10808 0 1);
      pure ()
    pat_end;
    pattern fun (v_2681 : reg (bv 16)) (v_2680 : Mem) => do
      v_10836 <- evaluateAddress v_2680;
      v_10837 <- getRegister v_2681;
      v_10839 <- load v_10836 2;
      v_10841 <- eval (add (concat (expression.bv_nat 1 0) v_10837) (concat (expression.bv_nat 1 0) v_10839));
      v_10842 <- eval (extract v_10841 1 17);
      store v_10836 v_10842 2;
      v_10845 <- eval (extract v_10841 1 2);
      v_10854 <- eval (eq (extract v_10837 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10854 (eq (extract v_10839 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10854 (eq v_10845 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10841 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10837 v_10839) 11 12) (extract v_10841 12 13));
      setRegister zf (zeroFlag v_10842);
      setRegister sf v_10845;
      setRegister cf (extract v_10841 0 1);
      pure ()
    pat_end
