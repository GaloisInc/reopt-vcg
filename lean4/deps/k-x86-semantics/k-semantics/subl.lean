def subl1 : instruction :=
  definst "subl" $ do
    pattern fun (v_3148 : imm int) eax => do
      v_7087 <- eval (handleImmediateWithSignExtend v_3148 32 32);
      v_7093 <- getRegister rax;
      v_7096 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7087 (mi (bitwidthMInt v_7087) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) (extract v_7093 32 64)));
      v_7101 <- eval (extract v_7096 1 2);
      v_7107 <- eval (extract v_7096 1 33);
      v_7111 <- eval (extract v_7087 0 1);
      v_7115 <- eval (eq (bv_xor v_7111 (mi (bitwidthMInt v_7111) -1)) (expression.bv_nat 1 1));
      setRegister eax v_7107;
      setRegister of (mux (bit_and (eq v_7115 (eq (extract v_7093 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_7115 (eq v_7101 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7096 25 33));
      setRegister zf (zeroFlag v_7107);
      setRegister af (bv_xor (bv_xor (extract v_7087 27 28) (extract v_7093 59 60)) (extract v_7096 28 29));
      setRegister sf v_7101;
      setRegister cf (mux (notBool_ (eq (extract v_7096 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3160 : imm int) (v_3162 : reg (bv 32)) => do
      v_7139 <- eval (handleImmediateWithSignExtend v_3160 32 32);
      v_7145 <- getRegister v_3162;
      v_7147 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7139 (mi (bitwidthMInt v_7139) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_7145));
      v_7152 <- eval (extract v_7147 1 2);
      v_7153 <- eval (extract v_7147 1 33);
      v_7161 <- eval (extract v_7139 0 1);
      v_7165 <- eval (eq (bv_xor v_7161 (mi (bitwidthMInt v_7161) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3162) v_7153;
      setRegister of (mux (bit_and (eq v_7165 (eq (extract v_7145 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7165 (eq v_7152 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7147 25 33));
      setRegister af (bv_xor (extract (bv_xor v_7139 v_7145) 27 28) (extract v_7147 28 29));
      setRegister zf (zeroFlag v_7153);
      setRegister sf v_7152;
      setRegister cf (mux (notBool_ (eq (extract v_7147 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3170 : reg (bv 32)) (v_3171 : reg (bv 32)) => do
      v_7185 <- getRegister v_3170;
      v_7191 <- getRegister v_3171;
      v_7193 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7185 (mi (bitwidthMInt v_7185) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_7191));
      v_7198 <- eval (extract v_7193 1 2);
      v_7199 <- eval (extract v_7193 1 33);
      v_7207 <- eval (extract v_7185 0 1);
      v_7211 <- eval (eq (bv_xor v_7207 (mi (bitwidthMInt v_7207) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3171) v_7199;
      setRegister of (mux (bit_and (eq v_7211 (eq (extract v_7191 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7211 (eq v_7198 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7193 25 33));
      setRegister af (bv_xor (extract (bv_xor v_7185 v_7191) 27 28) (extract v_7193 28 29));
      setRegister zf (zeroFlag v_7199);
      setRegister sf v_7198;
      setRegister cf (mux (notBool_ (eq (extract v_7193 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3165 : Mem) (v_3166 : reg (bv 32)) => do
      v_10374 <- evaluateAddress v_3165;
      v_10375 <- load v_10374 4;
      v_10381 <- getRegister v_3166;
      v_10383 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10375 (mi (bitwidthMInt v_10375) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_10381));
      v_10388 <- eval (extract v_10383 1 2);
      v_10389 <- eval (extract v_10383 1 33);
      v_10397 <- eval (extract v_10375 0 1);
      v_10401 <- eval (eq (bv_xor v_10397 (mi (bitwidthMInt v_10397) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3166) v_10389;
      setRegister of (mux (bit_and (eq v_10401 (eq (extract v_10381 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10401 (eq v_10388 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10383 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10375 v_10381) 27 28) (extract v_10383 28 29));
      setRegister zf (zeroFlag v_10389);
      setRegister sf v_10388;
      setRegister cf (mux (notBool_ (eq (extract v_10383 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3153 : imm int) (v_3152 : Mem) => do
      v_13075 <- evaluateAddress v_3152;
      v_13076 <- eval (handleImmediateWithSignExtend v_3153 32 32);
      v_13082 <- load v_13075 4;
      v_13084 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13076 (mi (bitwidthMInt v_13076) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_13082));
      v_13085 <- eval (extract v_13084 1 33);
      store v_13075 v_13085 4;
      v_13091 <- eval (extract v_13084 1 2);
      v_13099 <- eval (extract v_13076 0 1);
      v_13103 <- eval (eq (bv_xor v_13099 (mi (bitwidthMInt v_13099) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13103 (eq (extract v_13082 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13103 (eq v_13091 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13084 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13076 v_13082) 27 28) (extract v_13084 28 29));
      setRegister zf (zeroFlag v_13085);
      setRegister sf v_13091;
      setRegister cf (mux (notBool_ (eq (extract v_13084 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3157 : reg (bv 32)) (v_3156 : Mem) => do
      v_13118 <- evaluateAddress v_3156;
      v_13119 <- getRegister v_3157;
      v_13125 <- load v_13118 4;
      v_13127 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13119 (mi (bitwidthMInt v_13119) -1))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_13125));
      v_13128 <- eval (extract v_13127 1 33);
      store v_13118 v_13128 4;
      v_13134 <- eval (extract v_13127 1 2);
      v_13142 <- eval (extract v_13119 0 1);
      v_13146 <- eval (eq (bv_xor v_13142 (mi (bitwidthMInt v_13142) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13146 (eq (extract v_13125 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13146 (eq v_13134 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13127 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13119 v_13125) 27 28) (extract v_13127 28 29));
      setRegister zf (zeroFlag v_13128);
      setRegister sf v_13134;
      setRegister cf (mux (notBool_ (eq (extract v_13127 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
