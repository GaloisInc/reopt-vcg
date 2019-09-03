def vpunpckhdq1 : instruction :=
  definst "vpunpckhdq" $ do
    pattern fun (v_2612 : reg (bv 128)) (v_2613 : reg (bv 128)) (v_2614 : reg (bv 128)) => do
      v_6130 <- getRegister v_2612;
      v_6132 <- getRegister v_2613;
      setRegister (lhs.of_reg v_2614) (concat (concat (extract v_6130 0 32) (extract v_6132 0 32)) (concat (extract v_6130 32 64) (extract v_6132 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2623 : reg (bv 256)) (v_2624 : reg (bv 256)) (v_2625 : reg (bv 256)) => do
      v_6145 <- getRegister v_2623;
      v_6147 <- getRegister v_2624;
      setRegister (lhs.of_reg v_2625) (concat (concat (extract v_6145 0 32) (extract v_6147 0 32)) (concat (concat (extract v_6145 32 64) (extract v_6147 32 64)) (concat (concat (extract v_6145 128 160) (extract v_6147 128 160)) (concat (extract v_6145 160 192) (extract v_6147 160 192)))));
      pure ()
    pat_end;
    pattern fun (v_2607 : Mem) (v_2608 : reg (bv 128)) (v_2609 : reg (bv 128)) => do
      v_12585 <- evaluateAddress v_2607;
      v_12586 <- load v_12585 16;
      v_12588 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2609) (concat (concat (extract v_12586 0 32) (extract v_12588 0 32)) (concat (extract v_12586 32 64) (extract v_12588 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2618 : Mem) (v_2619 : reg (bv 256)) (v_2620 : reg (bv 256)) => do
      v_12596 <- evaluateAddress v_2618;
      v_12597 <- load v_12596 32;
      v_12599 <- getRegister v_2619;
      setRegister (lhs.of_reg v_2620) (concat (concat (extract v_12597 0 32) (extract v_12599 0 32)) (concat (concat (extract v_12597 32 64) (extract v_12599 32 64)) (concat (concat (extract v_12597 128 160) (extract v_12599 128 160)) (concat (extract v_12597 160 192) (extract v_12599 160 192)))));
      pure ()
    pat_end
