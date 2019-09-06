def vpmovsxbq1 : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (v_2701 : reg (bv 128)) (v_2702 : reg (bv 128)) => do
      v_5541 <- getRegister v_2701;
      setRegister (lhs.of_reg v_2702) (concat (sext (extract v_5541 112 120) 64) (sext (extract v_5541 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2711 : reg (bv 128)) (v_2710 : reg (bv 256)) => do
      v_5552 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2710) (concat (sext (extract v_5552 96 104) 64) (concat (sext (extract v_5552 104 112) 64) (concat (sext (extract v_5552 112 120) 64) (sext (extract v_5552 120 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2697 : reg (bv 128)) => do
      v_11966 <- evaluateAddress v_2696;
      v_11967 <- load v_11966 2;
      setRegister (lhs.of_reg v_2697) (concat (sext (extract v_11967 0 8) 64) (sext (extract v_11967 8 16) 64));
      pure ()
    pat_end;
    pattern fun (v_2705 : Mem) (v_2706 : reg (bv 256)) => do
      v_11974 <- evaluateAddress v_2705;
      v_11975 <- load v_11974 4;
      setRegister (lhs.of_reg v_2706) (concat (sext (extract v_11975 0 8) 64) (concat (sext (extract v_11975 8 16) 64) (concat (sext (extract v_11975 16 24) 64) (sext (extract v_11975 24 32) 64))));
      pure ()
    pat_end
