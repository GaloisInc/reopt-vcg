def vpmovsxbq1 : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (v_2621 : reg (bv 128)) (v_2622 : reg (bv 128)) => do
      v_5463 <- getRegister v_2621;
      setRegister (lhs.of_reg v_2622) (concat (leanSignExtend (extract v_5463 112 120) 64) (leanSignExtend (extract v_5463 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2630 : reg (bv 128)) (v_2632 : reg (bv 256)) => do
      v_5474 <- getRegister v_2630;
      setRegister (lhs.of_reg v_2632) (concat (leanSignExtend (extract v_5474 96 104) 64) (concat (leanSignExtend (extract v_5474 104 112) 64) (concat (leanSignExtend (extract v_5474 112 120) 64) (leanSignExtend (extract v_5474 120 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2616 : Mem) (v_2617 : reg (bv 128)) => do
      v_12144 <- evaluateAddress v_2616;
      v_12145 <- load v_12144 2;
      setRegister (lhs.of_reg v_2617) (concat (leanSignExtend (extract v_12145 0 8) 64) (leanSignExtend (extract v_12145 8 16) 64));
      pure ()
    pat_end;
    pattern fun (v_2625 : Mem) (v_2627 : reg (bv 256)) => do
      v_12152 <- evaluateAddress v_2625;
      v_12153 <- load v_12152 4;
      setRegister (lhs.of_reg v_2627) (concat (leanSignExtend (extract v_12153 0 8) 64) (concat (leanSignExtend (extract v_12153 8 16) 64) (concat (leanSignExtend (extract v_12153 16 24) 64) (leanSignExtend (extract v_12153 24 32) 64))));
      pure ()
    pat_end
