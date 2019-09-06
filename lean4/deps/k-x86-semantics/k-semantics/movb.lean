def movb1 : instruction :=
  definst "movb" $ do
    pattern fun (v_3267 : imm int) (v_3269 : reg (bv 8)) => do
      setRegister (lhs.of_reg v_3269) (handleImmediateWithSignExtend v_3267 8 8);
      pure ()
    pat_end;
    pattern fun (v_3282 : reg (bv 8)) (v_3283 : reg (bv 8)) => do
      v_5775 <- getRegister v_3282;
      setRegister (lhs.of_reg v_3283) v_5775;
      pure ()
    pat_end;
    pattern fun (v_3236 : imm int) (v_3237 : Mem) => do
      v_7517 <- evaluateAddress v_3237;
      store v_7517 (handleImmediateWithSignExtend v_3236 8 8) 1;
      pure ()
    pat_end;
    pattern fun (v_3245 : reg (bv 8)) (v_3244 : Mem) => do
      v_7523 <- evaluateAddress v_3244;
      v_7524 <- getRegister v_3245;
      store v_7523 v_7524 1;
      pure ()
    pat_end;
    pattern fun (v_3272 : Mem) (v_3273 : reg (bv 8)) => do
      v_8965 <- evaluateAddress v_3272;
      v_8966 <- load v_8965 1;
      setRegister (lhs.of_reg v_3273) v_8966;
      pure ()
    pat_end
