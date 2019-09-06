def vpunpckhqdq1 : instruction :=
  definst "vpunpckhqdq" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 128)) (v_2717 : reg (bv 128)) => do
      v_6244 <- getRegister v_2715;
      v_6246 <- getRegister v_2716;
      setRegister (lhs.of_reg v_2717) (concat (extract v_6244 0 64) (extract v_6246 0 64));
      pure ()
    pat_end;
    pattern fun (v_2726 : reg (bv 256)) (v_2727 : reg (bv 256)) (v_2728 : reg (bv 256)) => do
      v_6255 <- getRegister v_2726;
      v_6257 <- getRegister v_2727;
      setRegister (lhs.of_reg v_2728) (concat (concat (extract v_6255 0 64) (extract v_6257 0 64)) (concat (extract v_6255 128 192) (extract v_6257 128 192)));
      pure ()
    pat_end;
    pattern fun (v_2709 : Mem) (v_2710 : reg (bv 128)) (v_2711 : reg (bv 128)) => do
      v_12318 <- evaluateAddress v_2709;
      v_12319 <- load v_12318 16;
      v_12321 <- getRegister v_2710;
      setRegister (lhs.of_reg v_2711) (concat (extract v_12319 0 64) (extract v_12321 0 64));
      pure ()
    pat_end;
    pattern fun (v_2720 : Mem) (v_2721 : reg (bv 256)) (v_2722 : reg (bv 256)) => do
      v_12325 <- evaluateAddress v_2720;
      v_12326 <- load v_12325 32;
      v_12328 <- getRegister v_2721;
      setRegister (lhs.of_reg v_2722) (concat (concat (extract v_12326 0 64) (extract v_12328 0 64)) (concat (extract v_12326 128 192) (extract v_12328 128 192)));
      pure ()
    pat_end
