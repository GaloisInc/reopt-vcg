def vpsrldq1 : instruction :=
  definst "vpsrldq" $ do
    pattern fun (v_3327 : imm int) (v_3329 : reg (bv 128)) (v_3330 : reg (bv 128)) => do
      v_8853 <- getRegister v_3329;
      v_8854 <- eval (handleImmediateWithSignExtend v_3327 8 8);
      v_8857 <- eval (mux (ugt v_8854 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8854));
      setRegister (lhs.of_reg v_3330) (lshr v_8853 (uvalueMInt (extract (shl v_8857 3) 0 (bitwidthMInt v_8857))));
      pure ()
    pat_end;
    pattern fun (v_3333 : imm int) (v_3336 : reg (bv 256)) (v_3337 : reg (bv 256)) => do
      v_8864 <- getRegister v_3336;
      v_8866 <- eval (handleImmediateWithSignExtend v_3333 8 8);
      v_8869 <- eval (mux (ugt v_8866 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_8866));
      v_8873 <- eval (uvalueMInt (extract (shl v_8869 3) 0 (bitwidthMInt v_8869)));
      setRegister (lhs.of_reg v_3337) (concat (lshr (extract v_8864 0 128) v_8873) (lshr (extract v_8864 128 256) v_8873));
      pure ()
    pat_end
