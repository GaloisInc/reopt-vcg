def vmovhps1 : instruction :=
  definst "vmovhps" $ do
    pattern fun (v_2824 : Mem) (v_2825 : reg (bv 128)) (v_2826 : reg (bv 128)) => do
      v_10315 <- evaluateAddress v_2824;
      v_10316 <- load v_10315 8;
      v_10317 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2826) (concat v_10316 (extract v_10317 64 128));
      pure ()
    pat_end;
    pattern fun (v_2821 : reg (bv 128)) (v_2820 : Mem) => do
      v_12744 <- evaluateAddress v_2820;
      v_12745 <- getRegister v_2821;
      store v_12744 (extract v_12745 0 64) 8;
      pure ()
    pat_end
