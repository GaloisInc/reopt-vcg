def vpsrldq1 : instruction :=
  definst "vpsrldq" $ do
    pattern fun (v_3318 : imm int) (v_3316 : reg (bv 128)) (v_3317 : reg (bv 128)) => do
      v_9331 <- getRegister v_3316;
      v_9332 <- eval (handleImmediateWithSignExtend v_3318 8 8);
      v_9335 <- eval (mux (ugt v_9332 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_9332));
      setRegister (lhs.of_reg v_3317) (lshr v_9331 (uvalueMInt (extract (shl v_9335 3) 0 (bitwidthMInt v_9335))));
      pure ()
    pat_end;
    pattern fun (v_3322 : imm int) (v_3323 : reg (bv 256)) (v_3324 : reg (bv 256)) => do
      v_9342 <- getRegister v_3323;
      v_9344 <- eval (handleImmediateWithSignExtend v_3322 8 8);
      v_9347 <- eval (mux (ugt v_9344 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_9344));
      v_9351 <- eval (uvalueMInt (extract (shl v_9347 3) 0 (bitwidthMInt v_9347)));
      setRegister (lhs.of_reg v_3324) (concat (lshr (extract v_9342 0 128) v_9351) (lshr (extract v_9342 128 256) v_9351));
      pure ()
    pat_end
