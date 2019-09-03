def vmovddup1 : instruction :=
  definst "vmovddup" $ do
    pattern fun (v_2752 : reg (bv 128)) (v_2753 : reg (bv 128)) => do
      v_5079 <- getRegister v_2752;
      setRegister (lhs.of_reg v_2753) (concat (extract v_5079 64 128) (extract v_5079 64 128));
      pure ()
    pat_end;
    pattern fun (v_2761 : reg (bv 256)) (v_2762 : reg (bv 256)) => do
      v_5087 <- getRegister v_2761;
      setRegister (lhs.of_reg v_2762) (concat (concat (extract v_5087 64 128) (extract v_5087 64 128)) (concat (extract v_5087 192 256) (extract v_5087 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2749 : reg (bv 128)) => do
      v_11086 <- evaluateAddress v_2748;
      v_11087 <- load v_11086 8;
      setRegister (lhs.of_reg v_2749) (concat v_11087 v_11087);
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) (v_2758 : reg (bv 256)) => do
      v_11090 <- evaluateAddress v_2757;
      v_11091 <- load v_11090 32;
      setRegister (lhs.of_reg v_2758) (concat (concat (extract v_11091 64 128) (extract v_11091 64 128)) (concat (extract v_11091 192 256) (extract v_11091 192 256)));
      pure ()
    pat_end
