def vpmovsxbd1 : instruction :=
  definst "vpmovsxbd" $ do
    pattern fun (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) => do
      v_5495 <- getRegister v_2683;
      setRegister (lhs.of_reg v_2684) (concat (sext (extract v_5495 96 104) 32) (concat (sext (extract v_5495 104 112) 32) (concat (sext (extract v_5495 112 120) 32) (sext (extract v_5495 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2693 : reg (bv 128)) (v_2692 : reg (bv 256)) => do
      v_5512 <- getRegister v_2693;
      setRegister (lhs.of_reg v_2692) (concat (sext (extract v_5512 64 72) 32) (concat (sext (extract v_5512 72 80) 32) (concat (sext (extract v_5512 80 88) 32) (concat (sext (extract v_5512 88 96) 32) (concat (sext (extract v_5512 96 104) 32) (concat (sext (extract v_5512 104 112) 32) (concat (sext (extract v_5512 112 120) 32) (sext (extract v_5512 120 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2678 : Mem) (v_2679 : reg (bv 128)) => do
      v_11926 <- evaluateAddress v_2678;
      v_11927 <- load v_11926 4;
      setRegister (lhs.of_reg v_2679) (concat (sext (extract v_11927 0 8) 32) (concat (sext (extract v_11927 8 16) 32) (concat (sext (extract v_11927 16 24) 32) (sext (extract v_11927 24 32) 32))));
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) (v_2688 : reg (bv 256)) => do
      v_11940 <- evaluateAddress v_2687;
      v_11941 <- load v_11940 8;
      setRegister (lhs.of_reg v_2688) (concat (sext (extract v_11941 0 8) 32) (concat (sext (extract v_11941 8 16) 32) (concat (sext (extract v_11941 16 24) 32) (concat (sext (extract v_11941 24 32) 32) (concat (sext (extract v_11941 32 40) 32) (concat (sext (extract v_11941 40 48) 32) (concat (sext (extract v_11941 48 56) 32) (sext (extract v_11941 56 64) 32))))))));
      pure ()
    pat_end
