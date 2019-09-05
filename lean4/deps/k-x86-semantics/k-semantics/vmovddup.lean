def vmovddup1 : instruction :=
  definst "vmovddup" $ do
    pattern fun (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) => do
      v_4764 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2804) (concat (extract v_4764 64 128) (extract v_4764 64 128));
      pure ()
    pat_end;
    pattern fun (v_2813 : reg (bv 256)) (v_2814 : reg (bv 256)) => do
      v_4772 <- getRegister v_2813;
      setRegister (lhs.of_reg v_2814) (concat (concat (extract v_4772 64 128) (extract v_4772 64 128)) (concat (extract v_4772 192 256) (extract v_4772 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2799 : Mem) (v_2800 : reg (bv 128)) => do
      v_10147 <- evaluateAddress v_2799;
      v_10148 <- load v_10147 8;
      setRegister (lhs.of_reg v_2800) (concat v_10148 v_10148);
      pure ()
    pat_end;
    pattern fun (v_2808 : Mem) (v_2809 : reg (bv 256)) => do
      v_10151 <- evaluateAddress v_2808;
      v_10152 <- load v_10151 32;
      setRegister (lhs.of_reg v_2809) (concat (concat (extract v_10152 64 128) (extract v_10152 64 128)) (concat (extract v_10152 192 256) (extract v_10152 192 256)));
      pure ()
    pat_end
