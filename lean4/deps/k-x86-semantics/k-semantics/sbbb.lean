def sbbb1 : instruction :=
  definst "sbbb" $ do
    pattern fun (v_3271 : imm int) (v_3273 : reg (bv 8)) => do
      v_7275 <- getRegister cf;
      v_7277 <- eval (handleImmediateWithSignExtend v_3271 8 8);
      v_7279 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7277 (expression.bv_nat 8 255)));
      v_7282 <- getRegister v_3273;
      v_7284 <- eval (add (mux (eq v_7275 (expression.bv_nat 1 1)) v_7279 (add v_7279 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_7282));
      v_7285 <- eval (extract v_7284 1 9);
      v_7287 <- eval (isBitSet v_7284 1);
      v_7291 <- eval (eq (bv_xor (extract v_7277 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3273) v_7285;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7277 v_7282) 3) (isBitSet v_7284 4)));
      setRegister cf (notBool_ (isBitSet v_7284 0));
      setRegister of (bit_and (eq v_7291 (isBitSet v_7282 0)) (notBool_ (eq v_7291 v_7287)));
      setRegister pf (parityFlag v_7285);
      setRegister sf v_7287;
      setRegister zf (zeroFlag v_7285);
      pure ()
    pat_end;
    pattern fun (v_3286 : reg (bv 8)) (v_3287 : reg (bv 8)) => do
      v_7351 <- getRegister cf;
      v_7353 <- getRegister v_3286;
      v_7355 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7353 (expression.bv_nat 8 255)));
      v_7358 <- getRegister v_3287;
      v_7360 <- eval (add (mux (eq v_7351 (expression.bv_nat 1 1)) v_7355 (add v_7355 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_7358));
      v_7361 <- eval (extract v_7360 1 9);
      v_7363 <- eval (isBitSet v_7360 1);
      v_7367 <- eval (eq (bv_xor (extract v_7353 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3287) v_7361;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7353 v_7358) 3) (isBitSet v_7360 4)));
      setRegister cf (notBool_ (isBitSet v_7360 0));
      setRegister of (bit_and (eq v_7367 (isBitSet v_7358 0)) (notBool_ (eq v_7367 v_7363)));
      setRegister pf (parityFlag v_7361);
      setRegister sf v_7363;
      setRegister zf (zeroFlag v_7361);
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 8)) => do
      v_11469 <- getRegister cf;
      v_11471 <- evaluateAddress v_3276;
      v_11472 <- load v_11471 1;
      v_11474 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_11472 (expression.bv_nat 8 255)));
      v_11477 <- getRegister v_3277;
      v_11479 <- eval (add (mux (eq v_11469 (expression.bv_nat 1 1)) v_11474 (add v_11474 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_11477));
      v_11480 <- eval (extract v_11479 1 9);
      v_11482 <- eval (isBitSet v_11479 1);
      v_11486 <- eval (eq (bv_xor (extract v_11472 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3277) v_11480;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11472 v_11477) 3) (isBitSet v_11479 4)));
      setRegister cf (notBool_ (isBitSet v_11479 0));
      setRegister of (bit_and (eq v_11486 (isBitSet v_11477 0)) (notBool_ (eq v_11486 v_11482)));
      setRegister pf (parityFlag v_11480);
      setRegister sf v_11482;
      setRegister zf (zeroFlag v_11480);
      pure ()
    pat_end;
    pattern fun (v_3240 : imm int) (v_3241 : Mem) => do
      v_14139 <- evaluateAddress v_3241;
      v_14140 <- getRegister cf;
      v_14142 <- eval (handleImmediateWithSignExtend v_3240 8 8);
      v_14144 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14142 (expression.bv_nat 8 255)));
      v_14147 <- load v_14139 1;
      v_14149 <- eval (add (mux (eq v_14140 (expression.bv_nat 1 1)) v_14144 (add v_14144 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_14147));
      v_14150 <- eval (extract v_14149 1 9);
      store v_14139 v_14150 1;
      v_14153 <- eval (isBitSet v_14149 1);
      v_14157 <- eval (eq (bv_xor (extract v_14142 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14142 v_14147) 3) (isBitSet v_14149 4)));
      setRegister cf (notBool_ (isBitSet v_14149 0));
      setRegister of (bit_and (eq v_14157 (isBitSet v_14147 0)) (notBool_ (eq v_14157 v_14153)));
      setRegister pf (parityFlag v_14150);
      setRegister sf v_14153;
      setRegister zf (zeroFlag v_14150);
      pure ()
    pat_end;
    pattern fun (v_3249 : reg (bv 8)) (v_3248 : Mem) => do
      v_14213 <- evaluateAddress v_3248;
      v_14214 <- getRegister cf;
      v_14216 <- getRegister v_3249;
      v_14218 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14216 (expression.bv_nat 8 255)));
      v_14221 <- load v_14213 1;
      v_14223 <- eval (add (mux (eq v_14214 (expression.bv_nat 1 1)) v_14218 (add v_14218 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_14221));
      v_14224 <- eval (extract v_14223 1 9);
      store v_14213 v_14224 1;
      v_14227 <- eval (isBitSet v_14223 1);
      v_14231 <- eval (eq (bv_xor (extract v_14216 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14216 v_14221) 3) (isBitSet v_14223 4)));
      setRegister cf (notBool_ (isBitSet v_14223 0));
      setRegister of (bit_and (eq v_14231 (isBitSet v_14221 0)) (notBool_ (eq v_14231 v_14227)));
      setRegister pf (parityFlag v_14224);
      setRegister sf v_14227;
      setRegister zf (zeroFlag v_14224);
      pure ()
    pat_end
