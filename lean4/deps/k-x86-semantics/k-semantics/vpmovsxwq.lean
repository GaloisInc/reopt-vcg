def vpmovsxwq1 : instruction :=
  definst "vpmovsxwq" $ do
    pattern fun (v_2746 : reg (bv 128)) (v_2747 : reg (bv 128)) => do
      v_5698 <- getRegister v_2746;
      setRegister (lhs.of_reg v_2747) (concat (sext (extract v_5698 96 112) 64) (sext (extract v_5698 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2756 : reg (bv 128)) (v_2755 : reg (bv 256)) => do
      v_5709 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2755) (concat (sext (extract v_5709 64 80) 64) (concat (sext (extract v_5709 80 96) 64) (concat (sext (extract v_5709 96 112) 64) (sext (extract v_5709 112 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) (v_2742 : reg (bv 128)) => do
      v_12099 <- evaluateAddress v_2741;
      v_12100 <- load v_12099 4;
      setRegister (lhs.of_reg v_2742) (concat (sext (extract v_12100 0 16) 64) (sext (extract v_12100 16 32) 64));
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2751 : reg (bv 256)) => do
      v_12107 <- evaluateAddress v_2750;
      v_12108 <- load v_12107 8;
      setRegister (lhs.of_reg v_2751) (concat (sext (extract v_12108 0 16) 64) (concat (sext (extract v_12108 16 32) 64) (concat (sext (extract v_12108 32 48) 64) (sext (extract v_12108 48 64) 64))));
      pure ()
    pat_end
