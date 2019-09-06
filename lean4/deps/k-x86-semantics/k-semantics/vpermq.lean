def vpermq1 : instruction :=
  definst "vpermq" $ do
    pattern fun (v_3173 : imm int) (v_3174 : reg (bv 256)) (v_3175 : reg (bv 256)) => do
      v_8577 <- getRegister v_3174;
      v_8578 <- eval (handleImmediateWithSignExtend v_3173 8 8);
      setRegister (lhs.of_reg v_3175) (concat (extract (lshr v_8577 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8578 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8577 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8578 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8577 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8578 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_8577 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8578 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3169 : imm int) (v_3168 : Mem) (v_3170 : reg (bv 256)) => do
      v_17075 <- evaluateAddress v_3168;
      v_17076 <- load v_17075 32;
      v_17077 <- eval (handleImmediateWithSignExtend v_3169 8 8);
      setRegister (lhs.of_reg v_3170) (concat (extract (lshr v_17076 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17077 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_17076 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17077 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_17076 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17077 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_17076 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17077 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end
