def vpunpckhdq1 : instruction :=
  definst "vpunpckhdq" $ do
    pattern fun (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) (v_2604 : reg (bv 128)) => do
      v_6265 <- getRegister v_2602;
      v_6267 <- getRegister v_2603;
      setRegister (lhs.of_reg v_2604) (concat (concat (extract v_6265 0 32) (extract v_6267 0 32)) (concat (extract v_6265 32 64) (extract v_6267 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2612 : reg (bv 256)) (v_2613 : reg (bv 256)) (v_2614 : reg (bv 256)) => do
      v_6280 <- getRegister v_2612;
      v_6282 <- getRegister v_2613;
      setRegister (lhs.of_reg v_2614) (concat (concat (extract v_6280 0 32) (extract v_6282 0 32)) (concat (concat (extract v_6280 32 64) (extract v_6282 32 64)) (concat (concat (extract v_6280 128 160) (extract v_6282 128 160)) (concat (extract v_6280 160 192) (extract v_6282 160 192)))));
      pure ()
    pat_end;
    pattern fun (v_2596 : Mem) (v_2597 : reg (bv 128)) (v_2598 : reg (bv 128)) => do
      v_12588 <- evaluateAddress v_2596;
      v_12589 <- load v_12588 16;
      v_12591 <- getRegister v_2597;
      setRegister (lhs.of_reg v_2598) (concat (concat (extract v_12589 0 32) (extract v_12591 0 32)) (concat (extract v_12589 32 64) (extract v_12591 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2607 : Mem) (v_2608 : reg (bv 256)) (v_2609 : reg (bv 256)) => do
      v_12599 <- evaluateAddress v_2607;
      v_12600 <- load v_12599 32;
      v_12602 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2609) (concat (concat (extract v_12600 0 32) (extract v_12602 0 32)) (concat (concat (extract v_12600 32 64) (extract v_12602 32 64)) (concat (concat (extract v_12600 128 160) (extract v_12602 128 160)) (concat (extract v_12600 160 192) (extract v_12602 160 192)))));
      pure ()
    pat_end
