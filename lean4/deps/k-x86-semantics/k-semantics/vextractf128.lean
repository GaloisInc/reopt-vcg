def vextractf1281 : instruction :=
  definst "vextractf128" $ do
    pattern fun (v_2386 : imm int) (v_2388 : reg (bv 256)) (v_2385 : reg (bv 128)) => do
      v_4002 <- getRegister v_2388;
      setRegister (lhs.of_reg v_2385) (mux (eq (extract (handleImmediateWithSignExtend v_2386 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_4002 128 256) (extract v_4002 0 128));
      pure ()
    pat_end;
    pattern fun (v_2380 : imm int) (v_2382 : reg (bv 256)) (v_2381 : Mem) => do
      v_13727 <- evaluateAddress v_2381;
      v_13731 <- getRegister v_2382;
      store v_13727 (mux (eq (extract (handleImmediateWithSignExtend v_2380 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_13731 128 256) (extract v_13731 0 128)) 16;
      pure ()
    pat_end
