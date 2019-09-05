def pmovsxbq1 : instruction :=
  definst "pmovsxbq" $ do
    pattern fun (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_5449 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2739) (concat (sext (extract v_5449 112 120) 64) (sext (extract v_5449 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2735 : Mem) (v_2734 : reg (bv 128)) => do
      v_12246 <- evaluateAddress v_2735;
      v_12247 <- load v_12246 2;
      setRegister (lhs.of_reg v_2734) (concat (sext (extract v_12247 0 8) 64) (sext (extract v_12247 8 16) 64));
      pure ()
    pat_end
