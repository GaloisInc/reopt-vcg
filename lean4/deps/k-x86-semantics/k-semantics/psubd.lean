def psubd1 : instruction :=
  definst "psubd" $ do
    pattern fun (v_3181 : reg (bv 128)) (v_3182 : reg (bv 128)) => do
      v_8043 <- getRegister v_3182;
      v_8045 <- getRegister v_3181;
      setRegister (lhs.of_reg v_3182) (concat (sub (extract v_8043 0 32) (extract v_8045 0 32)) (concat (sub (extract v_8043 32 64) (extract v_8045 32 64)) (concat (sub (extract v_8043 64 96) (extract v_8045 64 96)) (sub (extract v_8043 96 128) (extract v_8045 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3178 : reg (bv 128)) => do
      v_14470 <- getRegister v_3178;
      v_14472 <- evaluateAddress v_3177;
      v_14473 <- load v_14472 16;
      setRegister (lhs.of_reg v_3178) (concat (sub (extract v_14470 0 32) (extract v_14473 0 32)) (concat (sub (extract v_14470 32 64) (extract v_14473 32 64)) (concat (sub (extract v_14470 64 96) (extract v_14473 64 96)) (sub (extract v_14470 96 128) (extract v_14473 96 128)))));
      pure ()
    pat_end
