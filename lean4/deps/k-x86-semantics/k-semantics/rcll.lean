def rcll1 : instruction :=
  definst "rcll" $ do
    pattern fun cl (v_3295 : reg (bv 32)) => do
      v_9437 <- getRegister cf;
      v_9440 <- getRegister v_3295;
      v_9442 <- getRegister rcx;
      v_9446 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_9442 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9448 <- eval (rolHelper (concat (mux (eq v_9437 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9440) (uvalueMInt v_9446) 0);
      v_9449 <- eval (extract v_9448 0 1);
      v_9450 <- eval (extract v_9446 25 33);
      v_9451 <- eval (eq v_9450 (expression.bv_nat 8 1));
      v_9459 <- eval (eq v_9450 (expression.bv_nat 8 0));
      v_9462 <- getRegister of;
      setRegister (lhs.of_reg v_3295) (extract v_9448 1 33);
      setRegister of (mux (bit_or (bit_and v_9451 (notBool_ (eq (eq v_9449 (expression.bv_nat 1 1)) (eq (extract v_9448 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9451) (bit_or (bit_and (notBool_ v_9459) undef) (bit_and v_9459 (eq v_9462 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9449;
      pure ()
    pat_end;
    pattern fun (v_3299 : imm int) (v_3300 : reg (bv 32)) => do
      v_9473 <- getRegister cf;
      v_9476 <- getRegister v_3300;
      v_9481 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3299 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_9483 <- eval (rolHelper (concat (mux (eq v_9473 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9476) (uvalueMInt v_9481) 0);
      v_9484 <- eval (extract v_9483 0 1);
      v_9485 <- eval (extract v_9481 25 33);
      v_9486 <- eval (eq v_9485 (expression.bv_nat 8 1));
      v_9494 <- eval (eq v_9485 (expression.bv_nat 8 0));
      v_9497 <- getRegister of;
      setRegister (lhs.of_reg v_3300) (extract v_9483 1 33);
      setRegister of (mux (bit_or (bit_and v_9486 (notBool_ (eq (eq v_9484 (expression.bv_nat 1 1)) (eq (extract v_9483 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_9486) (bit_or (bit_and (notBool_ v_9494) undef) (bit_and v_9494 (eq v_9497 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9484;
      pure ()
    pat_end;
    pattern fun $0x1 (v_3304 : reg (bv 32)) => do
      v_9508 <- getRegister cf;
      v_9511 <- getRegister v_3304;
      v_9512 <- eval (concat (mux (eq v_9508 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_9511);
      v_9514 <- eval (bitwidthMInt v_9512);
      v_9520 <- eval (add (extract (shl v_9512 1) 0 v_9514) (concat (mi (sub v_9514 1) 0) (extract v_9512 0 1)));
      v_9521 <- eval (extract v_9520 0 1);
      setRegister (lhs.of_reg v_3304) (extract v_9520 1 33);
      setRegister of (mux (notBool_ (eq (eq v_9521 (expression.bv_nat 1 1)) (eq (extract v_9520 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_9521;
      pure ()
    pat_end;
    pattern fun cl (v_3284 : Mem) => do
      v_16245 <- evaluateAddress v_3284;
      v_16246 <- getRegister cf;
      v_16249 <- load v_16245 4;
      v_16251 <- getRegister rcx;
      v_16255 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_16251 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_16257 <- eval (rolHelper (concat (mux (eq v_16246 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_16249) (uvalueMInt v_16255) 0);
      store v_16245 (extract v_16257 1 33) 4;
      v_16260 <- eval (extract v_16257 0 1);
      v_16261 <- eval (extract v_16255 25 33);
      v_16262 <- eval (eq v_16261 (expression.bv_nat 8 1));
      v_16270 <- eval (eq v_16261 (expression.bv_nat 8 0));
      v_16273 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16262 (notBool_ (eq (eq v_16260 (expression.bv_nat 1 1)) (eq (extract v_16257 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_16262) (bit_or (bit_and (notBool_ v_16270) undef) (bit_and v_16270 (eq v_16273 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_16260;
      pure ()
    pat_end;
    pattern fun (v_3288 : imm int) (v_3287 : Mem) => do
      v_16282 <- evaluateAddress v_3287;
      v_16283 <- getRegister cf;
      v_16286 <- load v_16282 4;
      v_16291 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_3288 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_16293 <- eval (rolHelper (concat (mux (eq v_16283 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_16286) (uvalueMInt v_16291) 0);
      store v_16282 (extract v_16293 1 33) 4;
      v_16296 <- eval (extract v_16293 0 1);
      v_16297 <- eval (extract v_16291 25 33);
      v_16298 <- eval (eq v_16297 (expression.bv_nat 8 1));
      v_16306 <- eval (eq v_16297 (expression.bv_nat 8 0));
      v_16309 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16298 (notBool_ (eq (eq v_16296 (expression.bv_nat 1 1)) (eq (extract v_16293 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_16298) (bit_or (bit_and (notBool_ v_16306) undef) (bit_and v_16306 (eq v_16309 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_16296;
      pure ()
    pat_end
