def vpunpcklqdq1 : instruction :=
  definst "vpunpcklqdq" $ do
    pattern fun (v_2776 : reg (bv 128)) (v_2777 : reg (bv 128)) (v_2778 : reg (bv 128)) => do
      v_6453 <- getRegister v_2776;
      v_6455 <- getRegister v_2777;
      setRegister (lhs.of_reg v_2778) (concat (extract v_6453 64 128) (extract v_6455 64 128));
      pure ()
    pat_end;
    pattern fun (v_2787 : reg (bv 256)) (v_2788 : reg (bv 256)) (v_2789 : reg (bv 256)) => do
      v_6464 <- getRegister v_2787;
      v_6466 <- getRegister v_2788;
      setRegister (lhs.of_reg v_2789) (concat (concat (extract v_6464 64 128) (extract v_6466 64 128)) (concat (extract v_6464 192 256) (extract v_6466 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2770 : Mem) (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) => do
      v_12495 <- evaluateAddress v_2770;
      v_12496 <- load v_12495 16;
      v_12498 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2772) (concat (extract v_12496 64 128) (extract v_12498 64 128));
      pure ()
    pat_end;
    pattern fun (v_2781 : Mem) (v_2782 : reg (bv 256)) (v_2783 : reg (bv 256)) => do
      v_12502 <- evaluateAddress v_2781;
      v_12503 <- load v_12502 32;
      v_12505 <- getRegister v_2782;
      setRegister (lhs.of_reg v_2783) (concat (concat (extract v_12503 64 128) (extract v_12505 64 128)) (concat (extract v_12503 192 256) (extract v_12505 192 256)));
      pure ()
    pat_end
