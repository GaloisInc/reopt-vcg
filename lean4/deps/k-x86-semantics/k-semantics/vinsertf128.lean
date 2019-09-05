def vinsertf1281 : instruction :=
  definst "vinsertf128" $ do
    pattern fun (v_2516 : imm int) (v_2517 : reg (bv 128)) (v_2519 : reg (bv 256)) (v_2520 : reg (bv 256)) => do
      v_4250 <- getRegister v_2519;
      v_4252 <- getRegister v_2517;
      setRegister (lhs.of_reg v_2520) (mux (isBitClear (handleImmediateWithSignExtend v_2516 8 8) 7) (concat (extract v_4250 0 128) v_4252) (concat v_4252 (extract v_4250 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2510 : imm int) (v_2511 : Mem) (v_2512 : reg (bv 256)) (v_2513 : reg (bv 256)) => do
      v_9697 <- getRegister v_2512;
      v_9699 <- evaluateAddress v_2511;
      v_9700 <- load v_9699 16;
      setRegister (lhs.of_reg v_2513) (mux (isBitClear (handleImmediateWithSignExtend v_2510 8 8) 7) (concat (extract v_9697 0 128) v_9700) (concat v_9700 (extract v_9697 128 256)));
      pure ()
    pat_end
