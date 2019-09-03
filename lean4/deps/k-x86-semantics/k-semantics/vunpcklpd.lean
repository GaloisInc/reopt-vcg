def vunpcklpd1 : instruction :=
  definst "vunpcklpd" $ do
    pattern fun (v_2527 : reg (bv 128)) (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) => do
      v_3745 <- getRegister v_2527;
      v_3747 <- getRegister v_2528;
      setRegister (lhs.of_reg v_2529) (concat (extract v_3745 64 128) (extract v_3747 64 128));
      pure ()
    pat_end;
    pattern fun (v_2537 : reg (bv 256)) (v_2538 : reg (bv 256)) (v_2539 : reg (bv 256)) => do
      v_3756 <- getRegister v_2537;
      v_3758 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2539) (concat (concat (extract v_3756 64 128) (extract v_3758 64 128)) (concat (extract v_3756 192 256) (extract v_3758 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2520 : Mem) (v_2522 : reg (bv 128)) (v_2523 : reg (bv 128)) => do
      v_6980 <- evaluateAddress v_2520;
      v_6981 <- load v_6980 16;
      v_6983 <- getRegister v_2522;
      setRegister (lhs.of_reg v_2523) (concat (extract v_6981 64 128) (extract v_6983 64 128));
      pure ()
    pat_end;
    pattern fun (v_2531 : Mem) (v_2532 : reg (bv 256)) (v_2533 : reg (bv 256)) => do
      v_6987 <- evaluateAddress v_2531;
      v_6988 <- load v_6987 32;
      v_6990 <- getRegister v_2532;
      setRegister (lhs.of_reg v_2533) (concat (concat (extract v_6988 64 128) (extract v_6990 64 128)) (concat (extract v_6988 192 256) (extract v_6990 192 256)));
      pure ()
    pat_end
