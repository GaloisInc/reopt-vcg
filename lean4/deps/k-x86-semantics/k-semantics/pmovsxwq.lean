def pmovsxwq1 : instruction :=
  definst "pmovsxwq" $ do
    pattern fun (v_2725 : reg (bv 128)) (v_2726 : reg (bv 128)) => do
      v_5486 <- getRegister v_2725;
      setRegister (lhs.of_reg v_2726) (concat (leanSignExtend (extract v_5486 96 112) 64) (leanSignExtend (extract v_5486 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2721 : Mem) (v_2722 : reg (bv 128)) => do
      v_12444 <- evaluateAddress v_2721;
      v_12445 <- load v_12444 4;
      setRegister (lhs.of_reg v_2722) (concat (leanSignExtend (extract v_12445 0 16) 64) (leanSignExtend (extract v_12445 16 32) 64));
      pure ()
    pat_end
