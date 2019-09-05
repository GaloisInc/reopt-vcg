def sbbl1 : instruction :=
  definst "sbbl" $ do
    pattern fun (v_3304 : imm int) (v_3303 : reg (bv 32)) => do
      v_7435 <- getRegister cf;
      v_7437 <- eval (handleImmediateWithSignExtend v_3304 32 32);
      v_7439 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7437 (expression.bv_nat 32 4294967295)));
      v_7442 <- getRegister v_3303;
      v_7444 <- eval (add (mux (eq v_7435 (expression.bv_nat 1 1)) v_7439 (add v_7439 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_7442));
      v_7445 <- eval (extract v_7444 1 33);
      v_7447 <- eval (isBitSet v_7444 1);
      v_7452 <- eval (eq (bv_xor (extract v_7437 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3303) v_7445;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7437 v_7442) 27) (isBitSet v_7444 28)));
      setRegister cf (notBool_ (isBitSet v_7444 0));
      setRegister of (bit_and (eq v_7452 (isBitSet v_7442 0)) (notBool_ (eq v_7452 v_7447)));
      setRegister pf (parityFlag (extract v_7444 25 33));
      setRegister sf v_7447;
      setRegister zf (zeroFlag v_7445);
      pure ()
    pat_end;
    pattern fun (v_3312 : reg (bv 32)) (v_3313 : reg (bv 32)) => do
      v_7476 <- getRegister cf;
      v_7478 <- getRegister v_3312;
      v_7480 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7478 (expression.bv_nat 32 4294967295)));
      v_7483 <- getRegister v_3313;
      v_7485 <- eval (add (mux (eq v_7476 (expression.bv_nat 1 1)) v_7480 (add v_7480 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_7483));
      v_7486 <- eval (extract v_7485 1 33);
      v_7488 <- eval (isBitSet v_7485 1);
      v_7493 <- eval (eq (bv_xor (extract v_7478 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3313) v_7486;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7478 v_7483) 27) (isBitSet v_7485 28)));
      setRegister cf (notBool_ (isBitSet v_7485 0));
      setRegister of (bit_and (eq v_7493 (isBitSet v_7483 0)) (notBool_ (eq v_7493 v_7488)));
      setRegister pf (parityFlag (extract v_7485 25 33));
      setRegister sf v_7488;
      setRegister zf (zeroFlag v_7486);
      pure ()
    pat_end;
    pattern fun (v_3307 : Mem) (v_3308 : reg (bv 32)) => do
      v_11508 <- getRegister cf;
      v_11510 <- evaluateAddress v_3307;
      v_11511 <- load v_11510 4;
      v_11513 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_11511 (expression.bv_nat 32 4294967295)));
      v_11516 <- getRegister v_3308;
      v_11518 <- eval (add (mux (eq v_11508 (expression.bv_nat 1 1)) v_11513 (add v_11513 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_11516));
      v_11519 <- eval (extract v_11518 1 33);
      v_11521 <- eval (isBitSet v_11518 1);
      v_11526 <- eval (eq (bv_xor (extract v_11511 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3308) v_11519;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11511 v_11516) 27) (isBitSet v_11518 28)));
      setRegister cf (notBool_ (isBitSet v_11518 0));
      setRegister of (bit_and (eq v_11526 (isBitSet v_11516 0)) (notBool_ (eq v_11526 v_11521)));
      setRegister pf (parityFlag (extract v_11518 25 33));
      setRegister sf v_11521;
      setRegister zf (zeroFlag v_11519);
      pure ()
    pat_end;
    pattern fun (v_3295 : imm int) (v_3294 : Mem) => do
      v_14250 <- evaluateAddress v_3294;
      v_14251 <- getRegister cf;
      v_14253 <- eval (handleImmediateWithSignExtend v_3295 32 32);
      v_14255 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14253 (expression.bv_nat 32 4294967295)));
      v_14258 <- load v_14250 4;
      v_14260 <- eval (add (mux (eq v_14251 (expression.bv_nat 1 1)) v_14255 (add v_14255 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_14258));
      v_14261 <- eval (extract v_14260 1 33);
      store v_14250 v_14261 4;
      v_14264 <- eval (isBitSet v_14260 1);
      v_14269 <- eval (eq (bv_xor (extract v_14253 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14253 v_14258) 27) (isBitSet v_14260 28)));
      setRegister cf (notBool_ (isBitSet v_14260 0));
      setRegister of (bit_and (eq v_14269 (isBitSet v_14258 0)) (notBool_ (eq v_14269 v_14264)));
      setRegister pf (parityFlag (extract v_14260 25 33));
      setRegister sf v_14264;
      setRegister zf (zeroFlag v_14261);
      pure ()
    pat_end;
    pattern fun (v_3299 : reg (bv 32)) (v_3298 : Mem) => do
      v_14288 <- evaluateAddress v_3298;
      v_14289 <- getRegister cf;
      v_14291 <- getRegister v_3299;
      v_14293 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14291 (expression.bv_nat 32 4294967295)));
      v_14296 <- load v_14288 4;
      v_14298 <- eval (add (mux (eq v_14289 (expression.bv_nat 1 1)) v_14293 (add v_14293 (expression.bv_nat 33 1))) (concat (expression.bv_nat 1 0) v_14296));
      v_14299 <- eval (extract v_14298 1 33);
      store v_14288 v_14299 4;
      v_14302 <- eval (isBitSet v_14298 1);
      v_14307 <- eval (eq (bv_xor (extract v_14291 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14291 v_14296) 27) (isBitSet v_14298 28)));
      setRegister cf (notBool_ (isBitSet v_14298 0));
      setRegister of (bit_and (eq v_14307 (isBitSet v_14296 0)) (notBool_ (eq v_14307 v_14302)));
      setRegister pf (parityFlag (extract v_14298 25 33));
      setRegister sf v_14302;
      setRegister zf (zeroFlag v_14299);
      pure ()
    pat_end
