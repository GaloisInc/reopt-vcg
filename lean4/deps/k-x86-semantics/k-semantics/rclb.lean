def rclb1 : instruction :=
  definst "rclb" $ do
    pattern fun cl (v_3259 : reg (bv 8)) => do
      v_9237 <- getRegister cf;
      v_9240 <- getRegister v_3259;
      v_9242 <- getRegister rcx;
      v_9246 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_9242 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_9248 <- eval (rolHelper (concat (mux (eq v_9237 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9240) (uvalueMInt v_9246) 0);
      v_9249 <- eval (extract v_9248 0 1);
      v_9250 <- eval (extract v_9246 1 9);
      v_9251 <- eval (eq v_9250 (expression.bv_nat 8 1));
      v_9259 <- eval (eq v_9250 (expression.bv_nat 8 0));
      v_9262 <- getRegister of;
      setRegister (lhs.of_reg v_3259) (extract v_9248 1 9);
      setRegister of (mux (bit_or (bit_and v_9251 (notBool_ (eq (eq v_9249 (expression.bv_nat 1 1)) (eq (extract v_9248 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9251) (bit_or (bit_and (notBool_ v_9259) undef) (bit_and v_9259 (eq v_9262 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9249;
      pure ()
    pat_end;
    pattern fun (v_3263 : imm int) (v_3264 : reg (bv 8)) => do
      v_9273 <- getRegister cf;
      v_9276 <- getRegister v_3264;
      v_9281 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3263 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_9283 <- eval (rolHelper (concat (mux (eq v_9273 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9276) (uvalueMInt v_9281) 0);
      v_9284 <- eval (extract v_9283 0 1);
      v_9285 <- eval (extract v_9281 1 9);
      v_9286 <- eval (eq v_9285 (expression.bv_nat 8 1));
      v_9294 <- eval (eq v_9285 (expression.bv_nat 8 0));
      v_9297 <- getRegister of;
      setRegister (lhs.of_reg v_3264) (extract v_9283 1 9);
      setRegister of (mux (bit_or (bit_and v_9286 (notBool_ (eq (eq v_9284 (expression.bv_nat 1 1)) (eq (extract v_9283 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9286) (bit_or (bit_and (notBool_ v_9294) undef) (bit_and v_9294 (eq v_9297 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9284;
      pure ()
    pat_end;
    pattern fun $0x1 (v_3268 : reg (bv 8)) => do
      v_9308 <- getRegister cf;
      v_9311 <- getRegister v_3268;
      v_9312 <- eval (concat (mux (eq v_9308 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9311);
      v_9314 <- eval (bitwidthMInt v_9312);
      v_9320 <- eval (add (extract (shl v_9312 1) 0 v_9314) (concat (mi (sub v_9314 1) 0) (extract v_9312 0 1)));
      v_9321 <- eval (extract v_9320 0 1);
      setRegister (lhs.of_reg v_3268) (extract v_9320 1 9);
      setRegister of (mux (notBool_ (eq (eq v_9321 (expression.bv_nat 1 1)) (eq (extract v_9320 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9321;
      pure ()
    pat_end;
    pattern fun cl (v_3248 : Mem) => do
      v_16122 <- evaluateAddress v_3248;
      v_16123 <- getRegister cf;
      v_16126 <- load v_16122 1;
      v_16128 <- getRegister rcx;
      v_16132 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_16128 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_16134 <- eval (rolHelper (concat (mux (eq v_16123 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_16126) (uvalueMInt v_16132) 0);
      store v_16122 (extract v_16134 1 9) 1;
      v_16137 <- eval (extract v_16134 0 1);
      v_16138 <- eval (extract v_16132 1 9);
      v_16139 <- eval (eq v_16138 (expression.bv_nat 8 1));
      v_16147 <- eval (eq v_16138 (expression.bv_nat 8 0));
      v_16150 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16139 (notBool_ (eq (eq v_16137 (expression.bv_nat 1 1)) (eq (extract v_16134 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_16139) (bit_or (bit_and (notBool_ v_16147) undef) (bit_and v_16147 (eq v_16150 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_16137;
      pure ()
    pat_end;
    pattern fun (v_3252 : imm int) (v_3251 : Mem) => do
      v_16159 <- evaluateAddress v_3251;
      v_16160 <- getRegister cf;
      v_16163 <- load v_16159 1;
      v_16168 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3252 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_16170 <- eval (rolHelper (concat (mux (eq v_16160 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_16163) (uvalueMInt v_16168) 0);
      store v_16159 (extract v_16170 1 9) 1;
      v_16173 <- eval (extract v_16170 0 1);
      v_16174 <- eval (extract v_16168 1 9);
      v_16175 <- eval (eq v_16174 (expression.bv_nat 8 1));
      v_16183 <- eval (eq v_16174 (expression.bv_nat 8 0));
      v_16186 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16175 (notBool_ (eq (eq v_16173 (expression.bv_nat 1 1)) (eq (extract v_16170 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_16175) (bit_or (bit_and (notBool_ v_16183) undef) (bit_and v_16183 (eq v_16186 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_16173;
      pure ()
    pat_end
