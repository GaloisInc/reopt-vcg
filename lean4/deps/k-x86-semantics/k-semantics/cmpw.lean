def cmpw1 : instruction :=
  definst "cmpw" $ do
    pattern fun (v_2417 : imm int) ax => do
      v_3872 <- eval (handleImmediateWithSignExtend v_2417 16 16);
      v_3876 <- getRegister rax;
      v_3879 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3872 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) (extract v_3876 48 64)));
      v_3884 <- eval (extract v_3879 1 2);
      v_3896 <- eval (eq (bv_xor (extract v_3872 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3896 (eq (extract v_3876 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_3896 (eq v_3884 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3879 9 17));
      setRegister af (bv_xor (bv_xor (extract v_3872 11 12) (extract v_3876 59 60)) (extract v_3879 12 13));
      setRegister zf (zeroFlag (extract v_3879 1 17));
      setRegister sf v_3884;
      setRegister cf (mux (notBool_ (eq (extract v_3879 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2429 : imm int) (v_2432 : reg (bv 16)) => do
      v_3919 <- eval (handleImmediateWithSignExtend v_2429 16 16);
      v_3923 <- getRegister v_2432;
      v_3925 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3919 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3923));
      v_3930 <- eval (extract v_3925 1 2);
      v_3941 <- eval (eq (bv_xor (extract v_3919 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3941 (eq (extract v_3923 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3941 (eq v_3930 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3925 9 17));
      setRegister af (bv_xor (extract (bv_xor v_3919 v_3923) 11 12) (extract v_3925 12 13));
      setRegister zf (zeroFlag (extract v_3925 1 17));
      setRegister sf v_3930;
      setRegister cf (mux (notBool_ (eq (extract v_3925 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2440 : reg (bv 16)) (v_2441 : reg (bv 16)) => do
      v_3960 <- getRegister v_2440;
      v_3964 <- getRegister v_2441;
      v_3966 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3960 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3964));
      v_3971 <- eval (extract v_3966 1 2);
      v_3982 <- eval (eq (bv_xor (extract v_3960 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3982 (eq (extract v_3964 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3982 (eq v_3971 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3966 9 17));
      setRegister af (bv_xor (extract (bv_xor v_3960 v_3964) 11 12) (extract v_3966 12 13));
      setRegister zf (zeroFlag (extract v_3966 1 17));
      setRegister sf v_3971;
      setRegister cf (mux (notBool_ (eq (extract v_3966 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2422 : imm int) (v_2421 : Mem) => do
      v_8137 <- eval (handleImmediateWithSignExtend v_2422 16 16);
      v_8141 <- evaluateAddress v_2421;
      v_8142 <- load v_8141 2;
      v_8144 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8137 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_8142));
      v_8149 <- eval (extract v_8144 1 2);
      v_8160 <- eval (eq (bv_xor (extract v_8137 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8160 (eq (extract v_8142 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8160 (eq v_8149 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8144 9 17));
      setRegister af (bv_xor (extract (bv_xor v_8137 v_8142) 11 12) (extract v_8144 12 13));
      setRegister zf (zeroFlag (extract v_8144 1 17));
      setRegister sf v_8149;
      setRegister cf (mux (notBool_ (eq (extract v_8144 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2427 : reg (bv 16)) (v_2425 : Mem) => do
      v_8175 <- getRegister v_2427;
      v_8179 <- evaluateAddress v_2425;
      v_8180 <- load v_8179 2;
      v_8182 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8175 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_8180));
      v_8187 <- eval (extract v_8182 1 2);
      v_8198 <- eval (eq (bv_xor (extract v_8175 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8198 (eq (extract v_8180 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8198 (eq v_8187 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8182 9 17));
      setRegister af (bv_xor (extract (bv_xor v_8175 v_8180) 11 12) (extract v_8182 12 13));
      setRegister zf (zeroFlag (extract v_8182 1 17));
      setRegister sf v_8187;
      setRegister cf (mux (notBool_ (eq (extract v_8182 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2434 : Mem) (v_2436 : reg (bv 16)) => do
      v_8213 <- evaluateAddress v_2434;
      v_8214 <- load v_8213 2;
      v_8218 <- getRegister v_2436;
      v_8220 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8214 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_8218));
      v_8225 <- eval (extract v_8220 1 2);
      v_8236 <- eval (eq (bv_xor (extract v_8214 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8236 (eq (extract v_8218 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8236 (eq v_8225 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8220 9 17));
      setRegister af (bv_xor (extract (bv_xor v_8214 v_8218) 11 12) (extract v_8220 12 13));
      setRegister zf (zeroFlag (extract v_8220 1 17));
      setRegister sf v_8225;
      setRegister cf (mux (notBool_ (eq (extract v_8220 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
