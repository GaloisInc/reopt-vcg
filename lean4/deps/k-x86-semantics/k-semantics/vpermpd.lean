def vpermpd1 : instruction :=
  definst "vpermpd" $ do
    pattern fun (v_3124 : imm int) (v_3125 : reg (bv 256)) (v_3126 : reg (bv 256)) => do
      v_8460 <- getRegister v_3125;
      v_8461 <- eval (handleImmediateWithSignExtend v_3124 8 8);
      setRegister (lhs.of_reg v_3126) (concat (extract (lshr v_8460 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8461 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8460 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8461 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8460 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8461 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_8460 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8461 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3119 : imm int) (v_3120 : Mem) (v_3121 : reg (bv 256)) => do
      v_16966 <- evaluateAddress v_3120;
      v_16967 <- load v_16966 32;
      v_16968 <- eval (handleImmediateWithSignExtend v_3119 8 8);
      setRegister (lhs.of_reg v_3121) (concat (extract (lshr v_16967 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16968 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_16967 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16968 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_16967 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16968 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_16967 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16968 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end
