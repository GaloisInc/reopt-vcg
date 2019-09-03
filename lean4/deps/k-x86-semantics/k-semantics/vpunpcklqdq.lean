def vpunpcklqdq1 : instruction :=
  definst "vpunpcklqdq" $ do
    pattern fun (v_2712 : reg (bv 128)) (v_2713 : reg (bv 128)) (v_2714 : reg (bv 128)) => do
      v_6539 <- getRegister v_2712;
      v_6541 <- getRegister v_2713;
      setRegister (lhs.of_reg v_2714) (concat (extract v_6539 64 128) (extract v_6541 64 128));
      pure ()
    pat_end;
    pattern fun (v_2722 : reg (bv 256)) (v_2723 : reg (bv 256)) (v_2724 : reg (bv 256)) => do
      v_6550 <- getRegister v_2722;
      v_6552 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2724) (concat (concat (extract v_6550 64 128) (extract v_6552 64 128)) (concat (extract v_6550 192 256) (extract v_6552 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 128)) (v_2708 : reg (bv 128)) => do
      v_12822 <- evaluateAddress v_2706;
      v_12823 <- load v_12822 16;
      v_12825 <- getRegister v_2707;
      setRegister (lhs.of_reg v_2708) (concat (extract v_12823 64 128) (extract v_12825 64 128));
      pure ()
    pat_end;
    pattern fun (v_2717 : Mem) (v_2718 : reg (bv 256)) (v_2719 : reg (bv 256)) => do
      v_12829 <- evaluateAddress v_2717;
      v_12830 <- load v_12829 32;
      v_12832 <- getRegister v_2718;
      setRegister (lhs.of_reg v_2719) (concat (concat (extract v_12830 64 128) (extract v_12832 64 128)) (concat (extract v_12830 192 256) (extract v_12832 192 256)));
      pure ()
    pat_end
