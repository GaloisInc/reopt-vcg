def rolq1 : instruction :=
  definst "rolq" $ do
    pattern fun cl (v_2686 : reg (bv 64)) => do
      v_4930 <- getRegister rcx;
      v_4932 <- eval (bv_and (extract v_4930 56 64) (expression.bv_nat 8 63));
      v_4933 <- eval (eq v_4932 (expression.bv_nat 8 1));
      v_4934 <- getRegister v_2686;
      v_4936 <- eval (rol v_4934 (concat (expression.bv_nat 56 0) v_4932));
      v_4938 <- eval (isBitSet v_4936 63);
      v_4943 <- eval (eq v_4932 (expression.bv_nat 8 0));
      v_4944 <- eval (notBool_ v_4943);
      v_4946 <- getRegister of;
      v_4953 <- getRegister cf;
      setRegister (lhs.of_reg v_2686) v_4936;
      setRegister cf (bit_or (bit_and v_4944 v_4938) (bit_and v_4943 (eq v_4953 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4933 (notBool_ (eq (isBitSet v_4936 0) v_4938))) (bit_and (notBool_ v_4933) (bit_or (bit_and v_4944 undef) (bit_and v_4943 (eq v_4946 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2689 : imm int) (v_2691 : reg (bv 64)) => do
      v_4961 <- eval (bv_and (handleImmediateWithSignExtend v_2689 8 8) (expression.bv_nat 8 63));
      v_4962 <- eval (eq v_4961 (expression.bv_nat 8 1));
      v_4963 <- getRegister v_2691;
      v_4965 <- eval (rol v_4963 (concat (expression.bv_nat 56 0) v_4961));
      v_4967 <- eval (isBitSet v_4965 63);
      v_4972 <- eval (eq v_4961 (expression.bv_nat 8 0));
      v_4973 <- eval (notBool_ v_4972);
      v_4975 <- getRegister of;
      v_4982 <- getRegister cf;
      setRegister (lhs.of_reg v_2691) v_4965;
      setRegister cf (bit_or (bit_and v_4973 v_4967) (bit_and v_4972 (eq v_4982 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4962 (notBool_ (eq (isBitSet v_4965 0) v_4967))) (bit_and (notBool_ v_4962) (bit_or (bit_and v_4973 undef) (bit_and v_4972 (eq v_4975 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2675 : Mem) => do
      v_12373 <- evaluateAddress v_2675;
      v_12374 <- load v_12373 8;
      v_12375 <- getRegister rcx;
      v_12377 <- eval (bv_and (extract v_12375 56 64) (expression.bv_nat 8 63));
      v_12379 <- eval (rol v_12374 (concat (expression.bv_nat 56 0) v_12377));
      store v_12373 v_12379 8;
      v_12381 <- eval (eq v_12377 (expression.bv_nat 8 1));
      v_12383 <- eval (isBitSet v_12379 63);
      v_12388 <- eval (eq v_12377 (expression.bv_nat 8 0));
      v_12389 <- eval (notBool_ v_12388);
      v_12391 <- getRegister of;
      v_12398 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12389 v_12383) (bit_and v_12388 (eq v_12398 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12381 (notBool_ (eq (isBitSet v_12379 0) v_12383))) (bit_and (notBool_ v_12381) (bit_or (bit_and v_12389 undef) (bit_and v_12388 (eq v_12391 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2678 : imm int) (v_2679 : Mem) => do
      v_12404 <- evaluateAddress v_2679;
      v_12405 <- load v_12404 8;
      v_12407 <- eval (bv_and (handleImmediateWithSignExtend v_2678 8 8) (expression.bv_nat 8 63));
      v_12409 <- eval (rol v_12405 (concat (expression.bv_nat 56 0) v_12407));
      store v_12404 v_12409 8;
      v_12411 <- eval (eq v_12407 (expression.bv_nat 8 1));
      v_12413 <- eval (isBitSet v_12409 63);
      v_12418 <- eval (eq v_12407 (expression.bv_nat 8 0));
      v_12419 <- eval (notBool_ v_12418);
      v_12421 <- getRegister of;
      v_12428 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12419 v_12413) (bit_and v_12418 (eq v_12428 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12411 (notBool_ (eq (isBitSet v_12409 0) v_12413))) (bit_and (notBool_ v_12411) (bit_or (bit_and v_12419 undef) (bit_and v_12418 (eq v_12421 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
