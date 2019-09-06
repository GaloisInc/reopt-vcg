def vpsrldq1 : instruction :=
  definst "vpsrldq" $ do
    pattern fun (v_3407 : imm int) (v_3409 : reg (bv 128)) (v_3410 : reg (bv 128)) => do
      v_8705 <- getRegister v_3409;
      v_8706 <- eval (handleImmediateWithSignExtend v_3407 8 8);
      setRegister (lhs.of_reg v_3410) (lshr v_8705 (extract (shl (mux (ugt v_8706 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8706)) (expression.bv_nat 128 3)) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3413 : imm int) (v_3415 : reg (bv 256)) (v_3416 : reg (bv 256)) => do
      v_8714 <- getRegister v_3415;
      v_8716 <- eval (handleImmediateWithSignExtend v_3413 8 8);
      v_8721 <- eval (extract (shl (mux (ugt v_8716 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8716)) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg v_3416) (concat (lshr (extract v_8714 0 128) v_8721) (lshr (extract v_8714 128 256) v_8721));
      pure ()
    pat_end
