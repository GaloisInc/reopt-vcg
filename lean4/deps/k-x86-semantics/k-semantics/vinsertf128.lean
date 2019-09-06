def vinsertf1281 : instruction :=
  definst "vinsertf128" $ do
    pattern fun (v_2541 : imm int) (v_2544 : reg (bv 128)) (v_2542 : reg (bv 256)) (v_2543 : reg (bv 256)) => do
      v_4277 <- getRegister v_2542;
      v_4279 <- getRegister v_2544;
      setRegister (lhs.of_reg v_2543) (mux (isBitClear (handleImmediateWithSignExtend v_2541 8 8) 7) (concat (extract v_4277 0 128) v_4279) (concat v_4279 (extract v_4277 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2535 : imm int) (v_2536 : Mem) (v_2537 : reg (bv 256)) (v_2538 : reg (bv 256)) => do
      v_9724 <- getRegister v_2537;
      v_9726 <- evaluateAddress v_2536;
      v_9727 <- load v_9726 16;
      setRegister (lhs.of_reg v_2538) (mux (isBitClear (handleImmediateWithSignExtend v_2535 8 8) 7) (concat (extract v_9724 0 128) v_9727) (concat v_9727 (extract v_9724 128 256)));
      pure ()
    pat_end
