def pmovsxbq1 : instruction :=
  definst "pmovsxbq" $ do
    pattern fun (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) => do
      v_5418 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2690) (concat (leanSignExtend (extract v_5418 112 120) 64) (leanSignExtend (extract v_5418 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2685 : Mem) (v_2686 : reg (bv 128)) => do
      v_12388 <- evaluateAddress v_2685;
      v_12389 <- load v_12388 2;
      setRegister (lhs.of_reg v_2686) (concat (leanSignExtend (extract v_12389 0 8) 64) (leanSignExtend (extract v_12389 8 16) 64));
      pure ()
    pat_end
