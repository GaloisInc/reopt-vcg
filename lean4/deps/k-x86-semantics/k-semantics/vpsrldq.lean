def vpsrldq1 : instruction :=
  definst "vpsrldq" $ do
    pattern fun (v_3378 : imm int) (v_3382 : reg (bv 128)) (v_3383 : reg (bv 128)) => do
      v_8678 <- getRegister v_3382;
      v_8679 <- eval (handleImmediateWithSignExtend v_3378 8 8);
      setRegister (lhs.of_reg v_3383) (lshr v_8678 (extract (shl (mux (ugt v_8679 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8679)) (expression.bv_nat 128 3)) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3384 : imm int) (v_3388 : reg (bv 256)) (v_3389 : reg (bv 256)) => do
      v_8687 <- getRegister v_3388;
      v_8689 <- eval (handleImmediateWithSignExtend v_3384 8 8);
      v_8694 <- eval (extract (shl (mux (ugt v_8689 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8689)) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg v_3389) (concat (lshr (extract v_8687 0 128) v_8694) (lshr (extract v_8687 128 256) v_8694));
      pure ()
    pat_end
