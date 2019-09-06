def psllq1 : instruction :=
  definst "psllq" $ do
    pattern fun (v_3065 : imm int) (v_3066 : reg (bv 128)) => do
      v_7617 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3065 8 8));
      v_7619 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3066) (mux (ugt v_7617 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7619 0 64) v_7617) 0 64) (extract (shl (extract v_7619 64 128) v_7617) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 128)) (v_3075 : reg (bv 128)) => do
      v_7633 <- getRegister v_3074;
      v_7634 <- eval (extract v_7633 64 128);
      v_7636 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3075) (mux (ugt v_7634 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7636 0 64) v_7634) 0 64) (extract (shl (extract v_7636 64 128) v_7634) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3070 : Mem) (v_3071 : reg (bv 128)) => do
      v_14238 <- evaluateAddress v_3070;
      v_14239 <- load v_14238 16;
      v_14240 <- eval (extract v_14239 64 128);
      v_14242 <- getRegister v_3071;
      setRegister (lhs.of_reg v_3071) (mux (ugt v_14240 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14242 0 64) v_14240) 0 64) (extract (shl (extract v_14242 64 128) v_14240) 0 64)));
      pure ()
    pat_end
