def subb1 : instruction :=
  definst "subb" $ do
    pattern fun (v_3107 : imm int) al => do
      v_6772 <- eval (handleImmediateWithSignExtend v_3107 8 8);
      v_6776 <- getRegister rax;
      v_6779 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6772 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) (extract v_6776 56 64)));
      v_6784 <- eval (extract v_6779 1 2);
      v_6790 <- eval (extract v_6779 1 9);
      v_6795 <- eval (eq (bv_xor (extract v_6772 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_6776 0 56) v_6790);
      setRegister of (mux (bit_and (eq v_6795 (eq (extract v_6776 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_6795 (eq v_6784 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6790);
      setRegister zf (zeroFlag v_6790);
      setRegister af (bv_xor (bv_xor (extract v_6772 3 4) (extract v_6776 59 60)) (extract v_6779 4 5));
      setRegister sf v_6784;
      setRegister cf (mux (notBool_ (eq (extract v_6779 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3123 : imm int) (v_3125 : reg (bv 8)) => do
      v_6825 <- eval (handleImmediateWithSignExtend v_3123 8 8);
      v_6829 <- getRegister v_3125;
      v_6831 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6825 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6829));
      v_6836 <- eval (extract v_6831 1 2);
      v_6841 <- eval (extract v_6831 1 9);
      v_6846 <- eval (eq (bv_xor (extract v_6825 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3125) v_6841;
      setRegister of (mux (bit_and (eq v_6846 (eq (extract v_6829 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_6846 (eq v_6836 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6841);
      setRegister zf (zeroFlag v_6841);
      setRegister af (bv_xor (extract (bv_xor v_6825 v_6829) 3 4) (extract v_6831 4 5));
      setRegister sf v_6836;
      setRegister cf (mux (notBool_ (eq (extract v_6831 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3133 : reg (bv 8)) (v_3134 : reg (bv 8)) => do
      v_6866 <- getRegister v_3133;
      v_6870 <- getRegister v_3134;
      v_6872 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6866 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6870));
      v_6877 <- eval (extract v_6872 1 2);
      v_6882 <- eval (extract v_6872 1 9);
      v_6887 <- eval (eq (bv_xor (extract v_6866 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3134) v_6882;
      setRegister of (mux (bit_and (eq v_6887 (eq (extract v_6870 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_6887 (eq v_6877 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6882);
      setRegister zf (zeroFlag v_6882);
      setRegister af (bv_xor (extract (bv_xor v_6866 v_6870) 3 4) (extract v_6872 4 5));
      setRegister sf v_6877;
      setRegister cf (mux (notBool_ (eq (extract v_6872 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3128 : Mem) (v_3129 : reg (bv 8)) => do
      v_10310 <- evaluateAddress v_3128;
      v_10311 <- load v_10310 1;
      v_10315 <- getRegister v_3129;
      v_10317 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10311 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10315));
      v_10322 <- eval (extract v_10317 1 2);
      v_10323 <- eval (extract v_10317 1 9);
      v_10332 <- eval (eq (bv_xor (extract v_10311 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3129) v_10323;
      setRegister of (mux (bit_and (eq v_10332 (eq (extract v_10315 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10332 (eq v_10322 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10323);
      setRegister af (bv_xor (extract (bv_xor v_10311 v_10315) 3 4) (extract v_10317 4 5));
      setRegister zf (zeroFlag v_10323);
      setRegister sf v_10322;
      setRegister cf (mux (notBool_ (eq (extract v_10317 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3148 : Mem) (v_3147 : reg (bv 8)) => do
      v_10348 <- evaluateAddress v_3148;
      v_10349 <- load v_10348 1;
      v_10353 <- getRegister v_3147;
      v_10355 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10349 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10353));
      v_10360 <- eval (extract v_10355 1 2);
      v_10365 <- eval (extract v_10355 1 9);
      v_10370 <- eval (eq (bv_xor (extract v_10349 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3147) v_10365;
      setRegister of (mux (bit_and (eq v_10370 (eq (extract v_10353 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10370 (eq v_10360 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10365);
      setRegister zf (zeroFlag v_10365);
      setRegister af (bv_xor (extract (bv_xor v_10349 v_10353) 3 4) (extract v_10355 4 5));
      setRegister sf v_10360;
      setRegister cf (mux (notBool_ (eq (extract v_10355 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3111 : imm int) (v_3112 : Mem) => do
      v_13021 <- evaluateAddress v_3112;
      v_13022 <- eval (handleImmediateWithSignExtend v_3111 8 8);
      v_13026 <- load v_13021 1;
      v_13028 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13022 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_13026));
      v_13029 <- eval (extract v_13028 1 9);
      store v_13021 v_13029 1;
      v_13035 <- eval (extract v_13028 1 2);
      v_13044 <- eval (eq (bv_xor (extract v_13022 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13044 (eq (extract v_13026 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13044 (eq v_13035 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13029);
      setRegister af (bv_xor (extract (bv_xor v_13022 v_13026) 3 4) (extract v_13028 4 5));
      setRegister zf (zeroFlag v_13029);
      setRegister sf v_13035;
      setRegister cf (mux (notBool_ (eq (extract v_13028 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3116 : reg (bv 8)) (v_3115 : Mem) => do
      v_13059 <- evaluateAddress v_3115;
      v_13060 <- getRegister v_3116;
      v_13064 <- load v_13059 1;
      v_13066 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13060 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_13064));
      v_13067 <- eval (extract v_13066 1 9);
      store v_13059 v_13067 1;
      v_13073 <- eval (extract v_13066 1 2);
      v_13082 <- eval (eq (bv_xor (extract v_13060 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13082 (eq (extract v_13064 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13082 (eq v_13073 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13067);
      setRegister af (bv_xor (extract (bv_xor v_13060 v_13064) 3 4) (extract v_13066 4 5));
      setRegister zf (zeroFlag v_13067);
      setRegister sf v_13073;
      setRegister cf (mux (notBool_ (eq (extract v_13066 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
