def vpunpckhbw1 : instruction :=
  definst "vpunpckhbw" $ do
    pattern fun (v_2580 : reg (bv 128)) (v_2581 : reg (bv 128)) (v_2582 : reg (bv 128)) => do
      v_6155 <- getRegister v_2580;
      v_6157 <- getRegister v_2581;
      setRegister (lhs.of_reg v_2582) (concat (concat (extract v_6155 0 8) (extract v_6157 0 8)) (concat (concat (extract v_6155 8 16) (extract v_6157 8 16)) (concat (concat (extract v_6155 16 24) (extract v_6157 16 24)) (concat (concat (extract v_6155 24 32) (extract v_6157 24 32)) (concat (concat (extract v_6155 32 40) (extract v_6157 32 40)) (concat (concat (extract v_6155 40 48) (extract v_6157 40 48)) (concat (concat (extract v_6155 48 56) (extract v_6157 48 56)) (concat (extract v_6155 56 64) (extract v_6157 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2590 : reg (bv 256)) (v_2591 : reg (bv 256)) (v_2592 : reg (bv 256)) => do
      v_6194 <- getRegister v_2590;
      v_6196 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2592) (concat (concat (extract v_6194 0 8) (extract v_6196 0 8)) (concat (concat (extract v_6194 8 16) (extract v_6196 8 16)) (concat (concat (extract v_6194 16 24) (extract v_6196 16 24)) (concat (concat (extract v_6194 24 32) (extract v_6196 24 32)) (concat (concat (extract v_6194 32 40) (extract v_6196 32 40)) (concat (concat (extract v_6194 40 48) (extract v_6196 40 48)) (concat (concat (extract v_6194 48 56) (extract v_6196 48 56)) (concat (concat (extract v_6194 56 64) (extract v_6196 56 64)) (concat (concat (extract v_6194 128 136) (extract v_6196 128 136)) (concat (concat (extract v_6194 136 144) (extract v_6196 136 144)) (concat (concat (extract v_6194 144 152) (extract v_6196 144 152)) (concat (concat (extract v_6194 152 160) (extract v_6196 152 160)) (concat (concat (extract v_6194 160 168) (extract v_6196 160 168)) (concat (concat (extract v_6194 168 176) (extract v_6196 168 176)) (concat (concat (extract v_6194 176 184) (extract v_6196 176 184)) (concat (extract v_6194 184 192) (extract v_6196 184 192)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 128)) (v_2576 : reg (bv 128)) => do
      v_12486 <- evaluateAddress v_2574;
      v_12487 <- load v_12486 16;
      v_12489 <- getRegister v_2575;
      setRegister (lhs.of_reg v_2576) (concat (concat (extract v_12487 0 8) (extract v_12489 0 8)) (concat (concat (extract v_12487 8 16) (extract v_12489 8 16)) (concat (concat (extract v_12487 16 24) (extract v_12489 16 24)) (concat (concat (extract v_12487 24 32) (extract v_12489 24 32)) (concat (concat (extract v_12487 32 40) (extract v_12489 32 40)) (concat (concat (extract v_12487 40 48) (extract v_12489 40 48)) (concat (concat (extract v_12487 48 56) (extract v_12489 48 56)) (concat (extract v_12487 56 64) (extract v_12489 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_2585 : Mem) (v_2586 : reg (bv 256)) (v_2587 : reg (bv 256)) => do
      v_12521 <- evaluateAddress v_2585;
      v_12522 <- load v_12521 32;
      v_12524 <- getRegister v_2586;
      setRegister (lhs.of_reg v_2587) (concat (concat (extract v_12522 0 8) (extract v_12524 0 8)) (concat (concat (extract v_12522 8 16) (extract v_12524 8 16)) (concat (concat (extract v_12522 16 24) (extract v_12524 16 24)) (concat (concat (extract v_12522 24 32) (extract v_12524 24 32)) (concat (concat (extract v_12522 32 40) (extract v_12524 32 40)) (concat (concat (extract v_12522 40 48) (extract v_12524 40 48)) (concat (concat (extract v_12522 48 56) (extract v_12524 48 56)) (concat (concat (extract v_12522 56 64) (extract v_12524 56 64)) (concat (concat (extract v_12522 128 136) (extract v_12524 128 136)) (concat (concat (extract v_12522 136 144) (extract v_12524 136 144)) (concat (concat (extract v_12522 144 152) (extract v_12524 144 152)) (concat (concat (extract v_12522 152 160) (extract v_12524 152 160)) (concat (concat (extract v_12522 160 168) (extract v_12524 160 168)) (concat (concat (extract v_12522 168 176) (extract v_12524 168 176)) (concat (concat (extract v_12522 176 184) (extract v_12524 176 184)) (concat (extract v_12522 184 192) (extract v_12524 184 192)))))))))))))))));
      pure ()
    pat_end
