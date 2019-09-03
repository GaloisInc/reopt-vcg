def pmovsxdq1 : instruction :=
  definst "pmovsxdq" $ do
    pattern fun (v_2707 : reg (bv 128)) (v_2708 : reg (bv 128)) => do
      v_5458 <- getRegister v_2707;
      setRegister (lhs.of_reg v_2708) (concat (leanSignExtend (extract v_5458 64 96) 64) (leanSignExtend (extract v_5458 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2703 : Mem) (v_2704 : reg (bv 128)) => do
      v_12422 <- evaluateAddress v_2703;
      v_12423 <- load v_12422 8;
      setRegister (lhs.of_reg v_2704) (concat (leanSignExtend (extract v_12423 0 32) 64) (leanSignExtend (extract v_12423 32 64) 64));
      pure ()
    pat_end
