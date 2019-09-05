def vpmovsxbq1 : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_5514 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2675) (concat (sext (extract v_5514 112 120) 64) (sext (extract v_5514 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2684 : reg (bv 128)) (v_2683 : reg (bv 256)) => do
      v_5525 <- getRegister v_2684;
      setRegister (lhs.of_reg v_2683) (concat (sext (extract v_5525 96 104) 64) (concat (sext (extract v_5525 104 112) 64) (concat (sext (extract v_5525 112 120) 64) (sext (extract v_5525 120 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2669 : Mem) (v_2670 : reg (bv 128)) => do
      v_11939 <- evaluateAddress v_2669;
      v_11940 <- load v_11939 2;
      setRegister (lhs.of_reg v_2670) (concat (sext (extract v_11940 0 8) 64) (sext (extract v_11940 8 16) 64));
      pure ()
    pat_end;
    pattern fun (v_2678 : Mem) (v_2679 : reg (bv 256)) => do
      v_11947 <- evaluateAddress v_2678;
      v_11948 <- load v_11947 4;
      setRegister (lhs.of_reg v_2679) (concat (sext (extract v_11948 0 8) 64) (concat (sext (extract v_11948 8 16) 64) (concat (sext (extract v_11948 16 24) 64) (sext (extract v_11948 24 32) 64))));
      pure ()
    pat_end
