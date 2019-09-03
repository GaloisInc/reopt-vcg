def pmuldq1 : instruction :=
  definst "pmuldq" $ do
    pattern fun (v_2788 : reg (bv 128)) (v_2789 : reg (bv 128)) => do
      v_5593 <- getRegister v_2789;
      v_5596 <- getRegister v_2788;
      setRegister (lhs.of_reg v_2789) (concat (mul (leanSignExtend (extract v_5593 32 64) 64) (leanSignExtend (extract v_5596 32 64) 64)) (mul (leanSignExtend (extract v_5593 96 128) 64) (leanSignExtend (extract v_5596 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2784 : Mem) (v_2785 : reg (bv 128)) => do
      v_12530 <- getRegister v_2785;
      v_12533 <- evaluateAddress v_2784;
      v_12534 <- load v_12533 16;
      setRegister (lhs.of_reg v_2785) (concat (mul (leanSignExtend (extract v_12530 32 64) 64) (leanSignExtend (extract v_12534 32 64) 64)) (mul (leanSignExtend (extract v_12530 96 128) 64) (leanSignExtend (extract v_12534 96 128) 64)));
      pure ()
    pat_end
