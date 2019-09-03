def vinsertf1281 : instruction :=
  definst "vinsertf128" $ do
    pattern fun (v_2468 : imm int) (v_2467 : reg (bv 128)) (v_2465 : reg (bv 256)) (v_2466 : reg (bv 256)) => do
      v_4560 <- getRegister v_2465;
      v_4562 <- getRegister v_2467;
      setRegister (lhs.of_reg v_2466) (mux (eq (extract (handleImmediateWithSignExtend v_2468 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_4560 0 128) v_4562) (concat v_4562 (extract v_4560 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2462 : imm int) (v_2459 : Mem) (v_2460 : reg (bv 256)) (v_2461 : reg (bv 256)) => do
      v_10613 <- getRegister v_2460;
      v_10615 <- evaluateAddress v_2459;
      v_10616 <- load v_10615 16;
      setRegister (lhs.of_reg v_2461) (mux (eq (extract (handleImmediateWithSignExtend v_2462 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_10613 0 128) v_10616) (concat v_10616 (extract v_10613 128 256)));
      pure ()
    pat_end
