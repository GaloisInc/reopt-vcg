def vmovddup1 : instruction :=
  definst "vmovddup" $ do
    pattern fun (v_2740 : reg (bv 128)) (v_2741 : reg (bv 128)) => do
      v_4706 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2741) (concat (extract v_4706 64 128) (extract v_4706 64 128));
      pure ()
    pat_end;
    pattern fun (v_2749 : reg (bv 256)) (v_2750 : reg (bv 256)) => do
      v_4714 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2750) (concat (concat (extract v_4714 64 128) (extract v_4714 64 128)) (concat (extract v_4714 192 256) (extract v_4714 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2735 : Mem) (v_2736 : reg (bv 128)) => do
      v_10281 <- evaluateAddress v_2735;
      v_10282 <- load v_10281 8;
      setRegister (lhs.of_reg v_2736) (concat v_10282 v_10282);
      pure ()
    pat_end;
    pattern fun (v_2744 : Mem) (v_2745 : reg (bv 256)) => do
      v_10285 <- evaluateAddress v_2744;
      v_10286 <- load v_10285 32;
      setRegister (lhs.of_reg v_2745) (concat (concat (extract v_10286 64 128) (extract v_10286 64 128)) (concat (extract v_10286 192 256) (extract v_10286 192 256)));
      pure ()
    pat_end
