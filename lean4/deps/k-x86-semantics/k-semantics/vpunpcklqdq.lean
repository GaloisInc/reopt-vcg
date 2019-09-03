def vpunpcklqdq1 : instruction :=
  definst "vpunpcklqdq" $ do
    pattern fun (v_2722 : reg (bv 128)) (v_2723 : reg (bv 128)) (v_2724 : reg (bv 128)) => do
      v_6404 <- getRegister v_2722;
      v_6406 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2724) (concat (extract v_6404 64 128) (extract v_6406 64 128));
      pure ()
    pat_end;
    pattern fun (v_2733 : reg (bv 256)) (v_2734 : reg (bv 256)) (v_2735 : reg (bv 256)) => do
      v_6415 <- getRegister v_2733;
      v_6417 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2735) (concat (concat (extract v_6415 64 128) (extract v_6417 64 128)) (concat (extract v_6415 192 256) (extract v_6417 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2717 : Mem) (v_2718 : reg (bv 128)) (v_2719 : reg (bv 128)) => do
      v_12819 <- evaluateAddress v_2717;
      v_12820 <- load v_12819 16;
      v_12822 <- getRegister v_2718;
      setRegister (lhs.of_reg v_2719) (concat (extract v_12820 64 128) (extract v_12822 64 128));
      pure ()
    pat_end;
    pattern fun (v_2728 : Mem) (v_2729 : reg (bv 256)) (v_2730 : reg (bv 256)) => do
      v_12826 <- evaluateAddress v_2728;
      v_12827 <- load v_12826 32;
      v_12829 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (concat (extract v_12827 64 128) (extract v_12829 64 128)) (concat (extract v_12827 192 256) (extract v_12829 192 256)));
      pure ()
    pat_end
